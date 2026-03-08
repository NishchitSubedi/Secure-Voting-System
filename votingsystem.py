import os
import sqlite3
import hmac
import hashlib
import base64
import secrets
import time
import json
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
from typing import Optional, List, Dict

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.backends import default_backend

_BACKEND      = default_backend()
AES_KEY_BYTES = 32
NONCE_BYTES   = 12
SALT_BYTES    = 32
PBKDF2_ITERS  = 390_000
REPLAY_WINDOW = 60

class CandidateHashTable:

    _DELETED = object()

    def __init__(self, capacity: int = 16):
        self._cap   = capacity
        self._keys  = [None] * self._cap
        self._vals  = [None] * self._cap
        self._count = 0
        self._LOAD  = 0.65

    def _hash(self, key: str) -> int:
        h = 0
        for ch in key:
            h = (h * 31 + ord(ch)) % self._cap
        return h

    def insert(self, candidate_id: str, name: str):
        if self._count / self._cap >= self._LOAD:
            self._resize()
        idx = self._hash(candidate_id)
        while True:
            slot = self._keys[idx]
            if slot is None or slot is self._DELETED:
                self._keys[idx] = candidate_id
                self._vals[idx] = name
                self._count += 1
                return
            if slot == candidate_id:
                self._vals[idx] = name
                return
            idx = (idx + 1) % self._cap

    def get(self, candidate_id: str, default=None):
        """O(1) average lookup."""
        idx = self._hash(candidate_id)
        probes = 0
        while self._keys[idx] is not None and probes < self._cap:
            if self._keys[idx] == candidate_id:
                return self._vals[idx]
            idx = (idx + 1) % self._cap
            probes += 1
        return default

    def delete(self, candidate_id: str):

        idx = self._hash(candidate_id)
        probes = 0
        while self._keys[idx] is not None and probes < self._cap:
            if self._keys[idx] == candidate_id:
                self._keys[idx] = self._DELETED
                self._vals[idx] = None
                self._count -= 1
                return
            idx = (idx + 1) % self._cap
            probes += 1

    def items(self):
        for k, v in zip(self._keys, self._vals):
            if k is not None and k is not self._DELETED:
                yield k, v

    def _resize(self):
        old_k, old_v = self._keys, self._vals
        self._cap *= 2
        self._keys  = [None] * self._cap
        self._vals  = [None] * self._cap
        self._count = 0
        for k, v in zip(old_k, old_v):
            if k is not None and k is not self._DELETED:
                self.insert(k, v)

    def __len__(self):        return self._count
    def __contains__(self, k): return self.get(k) is not None


class TallyNode:

    def __init__(self, candidate_id: str, name: str):
        self.candidate_id = candidate_id
        self.name  = name
        self.count = 0
        self.next  = None

    def to_dict(self):
        return {"candidate_id": self.candidate_id,
                "name": self.name, "count": self.count}


class VoteTallyList:


    def __init__(self):
        self._head = self._tail = None
        self._size = 0

    def add_candidate(self, candidate_id: str, name: str):
        cur = self._head
        while cur:
            if cur.candidate_id == candidate_id:
                return
            cur = cur.next
        node = TallyNode(candidate_id, name)
        if self._tail is None:
            self._head = self._tail = node
        else:
            self._tail.next = node
            self._tail = node
        self._size += 1

    def record_vote(self, candidate_id: str) -> bool:
        cur = self._head
        while cur:
            if cur.candidate_id == candidate_id:
                cur.count += 1
                return True
            cur = cur.next
        return False

    def sort_by_votes(self):
        self._head = self._merge_sort(self._head)
        cur = self._head
        self._tail = None
        while cur:
            self._tail = cur
            cur = cur.next

    def _merge_sort(self, head):
        if not head or not head.next:
            return head
        mid   = self._split(head)
        left  = self._merge_sort(head)
        right = self._merge_sort(mid)
        return self._merge(left, right)

    @staticmethod
    def _split(head):
        slow, fast = head, head.next
        while fast and fast.next:
            slow = slow.next
            fast = fast.next.next
        mid       = slow.next
        slow.next = None
        return mid

    @staticmethod
    def _merge(a, b):
        dummy = TallyNode("", "")
        cur   = dummy
        while a and b:
            if a.count >= b.count:
                cur.next, a = a, a.next
            else:
                cur.next, b = b, b.next
            cur = cur.next
        cur.next = a or b
        return dummy.next

    def to_list(self):
        result, cur = [], self._head
        while cur:
            result.append(cur.to_dict())
            cur = cur.next
        return result

    def winner(self): return self._head

    def __len__(self):  return self._size
    def __iter__(self):
        cur = self._head
        while cur:
            yield cur
            cur = cur.next


class VoterQueue:

    def __init__(self):
        self._data  = []
        self._front = 0

    def enqueue(self, voter_id: str):
        self._data.append(voter_id)

    def dequeue(self) -> str:
        if self.is_empty():
            raise IndexError("VoterQueue is empty")
        item        = self._data[self._front]
        self._front += 1
        if self._front > len(self._data) // 2:
            self._data  = self._data[self._front:]
            self._front = 0
        return item

    def peek(self) -> str:
        if self.is_empty():
            raise IndexError("VoterQueue is empty")
        return self._data[self._front]

    def is_empty(self) -> bool:
        return self._front >= len(self._data)

    def __len__(self):
        return len(self._data) - self._front


class AuditStack:

    def __init__(self, max_size: int = 1000):
        self._data = []
        self._max  = max_size

    def push(self, entry: dict):
        if len(self._data) >= self._max:
            self._data.pop(0)
        self._data.append(entry)

    def pop(self) -> dict:
        if not self._data:
            raise IndexError("AuditStack is empty")
        return self._data.pop()

    def peek(self) -> dict:
        if not self._data:
            raise IndexError("AuditStack is empty")
        return self._data[-1]

    def to_list(self):
        return list(reversed(self._data))

    def is_empty(self) -> bool: return len(self._data) == 0
    def __len__(self):          return len(self._data)


class BallotCipher:

    def __init__(self, key: bytes):
        if len(key) != AES_KEY_BYTES:
            raise ValueError(f"Key must be {AES_KEY_BYTES} bytes")
        self._aes = AESGCM(key)

    def encrypt(self, plaintext: bytes, aad: bytes = b"") -> bytes:
        nonce = os.urandom(NONCE_BYTES)
        ct    = self._aes.encrypt(nonce, plaintext, aad or None)
        return nonce + ct

    def decrypt(self, blob: bytes, aad: bytes = b"") -> bytes:
       
        return self._aes.decrypt(blob[:NONCE_BYTES], blob[NONCE_BYTES:], aad or None)

    @staticmethod
    def generate_key() -> bytes:
        return os.urandom(AES_KEY_BYTES)


class PasswordHasher:

    @staticmethod
    def hash_password(password: str) -> str:
        salt = os.urandom(SALT_BYTES)
        kdf  = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32,
                           salt=salt, iterations=PBKDF2_ITERS,
                           backend=_BACKEND)
        digest = kdf.derive(password.encode())
        return base64.b64encode(salt).decode() + ":" + base64.b64encode(digest).decode()

    @staticmethod
    def verify_password(password: str, stored: str) -> bool:
        try:
            salt_b64, digest_b64 = stored.split(":")
            salt   = base64.b64decode(salt_b64)
            expect = base64.b64decode(digest_b64)
        except Exception:
            return False
        kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32,
                          salt=salt, iterations=PBKDF2_ITERS,
                          backend=_BACKEND)
        try:
            kdf.verify(password.encode(), expect)
            return True
        except Exception:
            return False


class BallotSigner:

    def __init__(self, secret_key: bytes):
        self._key = secret_key

    def sign(self, data: bytes) -> bytes:
        return hmac.new(self._key, data, hashlib.sha256).digest()

    def verify(self, data: bytes, tag: bytes) -> bool:
        expected = hmac.new(self._key, data, hashlib.sha256).digest()
        return hmac.compare_digest(expected, tag)

    @staticmethod
    def ballot_payload(voter_id: str, election_id: str,
                       candidate: str, timestamp: float) -> bytes:
        return f"{voter_id}|{election_id}|{candidate}|{timestamp:.6f}".encode()


class NonceRegistry:

    def __init__(self, capacity: int = 256):
        self._cap  = capacity
        self._ring = [None] * capacity
        self._head = 0
        self._seen = set()

    def is_fresh(self, nonce: bytes, timestamp: float) -> bool:
        if abs(time.time() - timestamp) > REPLAY_WINDOW:
            return False
        if nonce in self._seen:
            return False
        self._store(nonce)
        return True

    def _store(self, nonce: bytes):
        evicted = self._ring[self._head]
        if evicted is not None:
            self._seen.discard(evicted)
        self._ring[self._head] = nonce
        self._seen.add(nonce)
        self._head = (self._head + 1) % self._cap

    def generate(self) -> bytes:
        return secrets.token_bytes(16)


class RateLimiter:

    def __init__(self, capacity: float = 5.0, rate: float = 0.5):
        self._cap     = capacity
        self._rate    = rate
        self._buckets = {}

    def is_allowed(self, voter_id: str) -> bool:
        now = time.monotonic()
        if voter_id not in self._buckets:
            self._buckets[voter_id] = [self._cap, now]
        tokens, last = self._buckets[voter_id]
        tokens = min(self._cap, tokens + (now - last) * self._rate)
        self._buckets[voter_id][1] = now
        if tokens >= 1.0:
            self._buckets[voter_id][0] = tokens - 1.0
            return True
        self._buckets[voter_id][0] = tokens
        return False

    def reset(self, voter_id: str):
        self._buckets.pop(voter_id, None)



_BASE_DIR  = os.path.dirname(os.path.abspath(__file__))
_SALT_FILE = os.path.join(_BASE_DIR, ".voting_salt")
_HMAC_FILE = os.path.join(_BASE_DIR, ".voting_hmac_key")


def _get_or_create(path: str) -> bytes:
    if os.path.exists(path):
        with open(path, "rb") as f:
            return f.read()
    key = os.urandom(AES_KEY_BYTES)
    with open(path, "wb") as f:
        f.write(key)
    return key


def get_storage_cipher() -> BallotCipher:
    """Derive a stable AES key from the persistent salt file."""
    salt = _get_or_create(_SALT_FILE)
    kdf  = PBKDF2HMAC(algorithm=hashes.SHA256(), length=AES_KEY_BYTES,
                       salt=salt, iterations=PBKDF2_ITERS, backend=_BACKEND)
    return BallotCipher(kdf.derive(b"voting-system-master-key-CW2"))


def get_ballot_signer() -> BallotSigner:
    return BallotSigner(_get_or_create(_HMAC_FILE))


DB_PATH = os.path.join(_BASE_DIR, "voting.db")


class VotingDatabase:

    def __init__(self, db_path: str = DB_PATH):
        self._db_path = db_path
        self._hasher  = PasswordHasher()
        self._cipher  = get_storage_cipher()
        self._signer  = get_ballot_signer()
        self._init_schema()

    def _connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self._db_path)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA foreign_keys=ON")
        return conn

    def _init_schema(self):
        with self._connect() as conn:
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS voters (
                    id         INTEGER PRIMARY KEY AUTOINCREMENT,
                    voter_id   TEXT    UNIQUE NOT NULL,
                    pwd_hash   TEXT    NOT NULL,
                    full_name  TEXT    NOT NULL,
                    is_admin   INTEGER NOT NULL DEFAULT 0,
                    registered REAL    NOT NULL,
                    last_login REAL
                );
                CREATE TABLE IF NOT EXISTS elections (
                    id         INTEGER PRIMARY KEY AUTOINCREMENT,
                    title      TEXT    NOT NULL,
                    candidates TEXT    NOT NULL,
                    status     TEXT    NOT NULL DEFAULT 'open',
                    created_by TEXT    NOT NULL,
                    created_at REAL    NOT NULL,
                    closed_at  REAL
                );
                CREATE TABLE IF NOT EXISTS ballots (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    voter_id    TEXT    NOT NULL,
                    election_id INTEGER NOT NULL,
                    encrypted   BLOB    NOT NULL,
                    hmac_tag    BLOB    NOT NULL,
                    nonce_hex   TEXT    NOT NULL,
                    timestamp   REAL    NOT NULL,
                    UNIQUE(voter_id, election_id)
                );
                CREATE TABLE IF NOT EXISTS audit_log (
                    id         INTEGER PRIMARY KEY AUTOINCREMENT,
                    event_type TEXT    NOT NULL,
                    actor      TEXT,
                    detail     TEXT,
                    timestamp  REAL    NOT NULL
                );
                CREATE INDEX IF NOT EXISTS idx_ballots_election
                    ON ballots(election_id);
            """)

   
    def register_voter(self, voter_id: str, password: str,
                       full_name: str, is_admin: bool = False) -> bool:
        if len(voter_id) < 4:
            raise ValueError("Voter ID must be at least 4 characters")
        if len(password) < 8:
            raise ValueError("Password must be at least 8 characters")
        if not full_name.strip():
            raise ValueError("Full name is required")
        pwd_hash = self._hasher.hash_password(password)
        try:
            with self._connect() as conn:
                conn.execute(
                    "INSERT INTO voters (voter_id,pwd_hash,full_name,is_admin,registered)"
                    " VALUES (?,?,?,?,?)",
                    (voter_id.lower(), pwd_hash, full_name.strip(),
                     int(is_admin), time.time()))
            self._log("REGISTER", voter_id, f"New voter: {full_name}")
            return True
        except sqlite3.IntegrityError:
            return False

    def authenticate(self, voter_id: str, password: str) -> Optional[Dict]:
        with self._connect() as conn:
            row = conn.execute("SELECT * FROM voters WHERE voter_id=?",
                               (voter_id.lower(),)).fetchone()
        if not row:
            return None
        if not self._hasher.verify_password(password, row["pwd_hash"]):
            self._log("FAILED_LOGIN", voter_id, "Wrong password")
            return None
        with self._connect() as conn:
            conn.execute("UPDATE voters SET last_login=? WHERE voter_id=?",
                         (time.time(), voter_id.lower()))
        self._log("LOGIN", voter_id, "Successful login")
        return dict(row)

    def voter_exists(self, voter_id: str) -> bool:
        with self._connect() as conn:
            r = conn.execute("SELECT 1 FROM voters WHERE voter_id=?",
                             (voter_id.lower(),)).fetchone()
        return r is not None

    def is_admin(self, voter_id: str) -> bool:
        with self._connect() as conn:
            r = conn.execute("SELECT is_admin FROM voters WHERE voter_id=?",
                             (voter_id.lower(),)).fetchone()
        return bool(r and r["is_admin"])

    
    def create_election(self, title: str, candidates: List[str],
                        created_by: str) -> int:
        if len(candidates) < 2:
            raise ValueError("An election needs at least 2 candidates")
        if not title.strip():
            raise ValueError("Election title cannot be empty")
        with self._connect() as conn:
            cur = conn.execute(
                "INSERT INTO elections (title,candidates,status,created_by,created_at)"
                " VALUES (?,?,?,?,?)",
                (title.strip(), json.dumps(candidates),
                 "open", created_by.lower(), time.time()))
            eid = cur.lastrowid
        self._log("CREATE_ELECTION", created_by, f"Election #{eid}: '{title}'")
        return eid

    def get_election(self, election_id: int) -> Optional[Dict]:
        with self._connect() as conn:
            row = conn.execute("SELECT * FROM elections WHERE id=?",
                               (election_id,)).fetchone()
        if not row:
            return None
        d = dict(row)
        d["candidates"] = json.loads(d["candidates"])
        return d

    def list_elections(self, status: str = None) -> List[Dict]:
        with self._connect() as conn:
            if status:
                rows = conn.execute(
                    "SELECT * FROM elections WHERE status=? ORDER BY id DESC",
                    (status,)).fetchall()
            else:
                rows = conn.execute(
                    "SELECT * FROM elections ORDER BY id DESC").fetchall()
        result = []
        for r in rows:
            d = dict(r)
            d["candidates"] = json.loads(d["candidates"])
            result.append(d)
        return result

    def close_election(self, election_id: int, admin_id: str):
        with self._connect() as conn:
            conn.execute(
                "UPDATE elections SET status='closed', closed_at=? WHERE id=?",
                (time.time(), election_id))
        self._log("CLOSE_ELECTION", admin_id, f"Closed election #{election_id}")

    
    def cast_vote(self, voter_id: str, election_id: int,
                  candidate: str, nonce: bytes) -> bool:

        ts       = time.time()
        election = self.get_election(election_id)
        if not election:
            raise ValueError("Election not found")
        if election["status"] != "open":
            raise ValueError("Election is not open")
        if candidate not in election["candidates"]:
            raise ValueError("Invalid candidate")

        aad       = f"{voter_id}:{election_id}".encode()
        encrypted = self._cipher.encrypt(candidate.encode(), aad)
        payload   = BallotSigner.ballot_payload(
            voter_id, str(election_id), candidate, ts)
        hmac_tag  = self._signer.sign(payload)

        try:
            with self._connect() as conn:
                conn.execute(
                    "INSERT INTO ballots"
                    " (voter_id,election_id,encrypted,hmac_tag,nonce_hex,timestamp)"
                    " VALUES (?,?,?,?,?,?)",
                    (voter_id.lower(), election_id,
                     encrypted, hmac_tag, nonce.hex(), ts))
            self._log("VOTE", voter_id, f"Voted in election #{election_id}")
            return True
        except sqlite3.IntegrityError:
            self._log("DOUBLE_VOTE_ATTEMPT", voter_id,
                      f"Tried to vote twice in #{election_id}")
            return False

    def has_voted(self, voter_id: str, election_id: int) -> bool:
        with self._connect() as conn:
            r = conn.execute(
                "SELECT 1 FROM ballots WHERE voter_id=? AND election_id=?",
                (voter_id.lower(), election_id)).fetchone()
        return r is not None

    def tally_votes(self, election_id: int) -> Dict[str, int]:
     
        election = self.get_election(election_id)
        if not election:
            raise ValueError("Election not found")
        tally = {c: 0 for c in election["candidates"]}
        with self._connect() as conn:
            rows = conn.execute(
                "SELECT * FROM ballots WHERE election_id=?",
                (election_id,)).fetchall()
        for row in rows:
            encrypted  = bytes(row["encrypted"])
            stored_tag = bytes(row["hmac_tag"])
            try:
                aad       = f"{row['voter_id']}:{election_id}".encode()
                candidate = self._cipher.decrypt(encrypted, aad).decode()
            except Exception:
                self._log("TAMPER_DETECTED", "SYSTEM",
                          f"Decryption failed for ballot id={row['id']}")
                continue
            payload = BallotSigner.ballot_payload(
                row["voter_id"], str(election_id), candidate, row["timestamp"])
            if not self._signer.verify(payload, stored_tag):
                self._log("TAMPER_DETECTED", "SYSTEM",
                          f"HMAC mismatch for ballot id={row['id']}")
                continue
            if candidate in tally:
                tally[candidate] += 1
        return tally

    def vote_count(self, election_id: int) -> int:
        with self._connect() as conn:
            r = conn.execute(
                "SELECT COUNT(*) as c FROM ballots WHERE election_id=?",
                (election_id,)).fetchone()
        return r["c"] if r else 0

    
    def _log(self, event_type: str, actor: str = None, detail: str = None):
        with self._connect() as conn:
            conn.execute(
                "INSERT INTO audit_log (event_type,actor,detail,timestamp)"
                " VALUES (?,?,?,?)",
                (event_type, actor, detail, time.time()))

    def get_audit_log(self, limit: int = 100) -> List[Dict]:
        with self._connect() as conn:
            rows = conn.execute(
                "SELECT * FROM audit_log ORDER BY id DESC LIMIT ?",
                (limit,)).fetchall()
        return [dict(r) for r in rows]

    def export_results_json(self, election_id: int, filepath: str):
        election = self.get_election(election_id)
        tally    = self.tally_votes(election_id)
        total    = sum(tally.values())
        winner   = max(tally, key=tally.get) if tally else "N/A"
        payload  = {"election": election, "tally": tally,
                    "total_votes": total, "winner": winner,
                    "exported_at": time.strftime("%Y-%m-%d %H:%M:%S")}
        with open(filepath, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)


BG       = "#0f172a"
SURFACE  = "#1e293b"
SURFACE2 = "#334155"
ACCENT   = "#6366f1"
ACCENT2  = "#10b981"
DANGER   = "#ef4444"
FG       = "#f1f5f9"
FG_DIM   = "#94a3b8"


def _label(parent, text, fg=FG, font=("Segoe UI", 10), bg=BG, **kw):
    return tk.Label(parent, text=text, fg=fg, font=font, bg=bg, **kw)

def _button(parent, text, command, bg=ACCENT, fg="white",
            font=("Segoe UI", 10, "bold"), **kw):
    return tk.Button(parent, text=text, command=command,
                     bg=bg, fg=fg, font=font, relief="flat",
                     cursor="hand2", activebackground=SURFACE2, **kw)

def _entry(parent, var, show="", width=28):
    return tk.Entry(parent, textvariable=var, show=show, width=width,
                    bg=SURFACE2, fg=FG, insertbackground=FG,
                    relief="flat", font=("Segoe UI", 11))

def _card(parent, padx=20, pady=16, bg=SURFACE):
    return tk.Frame(parent, bg=bg, padx=padx, pady=pady)

def _section_title(parent, text):
    tk.Label(parent, text=text, bg=BG, fg=ACCENT,
             font=("Segoe UI", 13, "bold")).pack(anchor="w", pady=(0, 8))




class LoginScreen(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("Secure Voting System")
        self.geometry("420x480")
        self.resizable(False, False)
        self.configure(bg=BG)

        self._db    = VotingDatabase()
        self._nonce = NonceRegistry()
        self._rl    = RateLimiter(capacity=5, rate=0.5)

        if not self._db.voter_exists("admin"):
            self._db.register_voter("admin", "Admin@1234",
                                    "System Administrator", is_admin=True)
        self._build_ui()

    def _build_ui(self):
        tk.Label(self, text="🗳  Secure Voting System",
                 bg=BG, fg=ACCENT,
                 font=("Segoe UI", 16, "bold")).pack(pady=(32, 4))
        tk.Label(self, text="Encrypted · Tamper-proof · Audited",
                 bg=BG, fg=FG_DIM,
                 font=("Segoe UI", 9)).pack(pady=(0, 20))

        card = _card(self)
        card.pack(fill="x", padx=40)

        def field(label, show=""):
            tk.Label(card, text=label, bg=SURFACE, fg=FG_DIM,
                     font=("Segoe UI", 9)).pack(anchor="w")
            var = tk.StringVar()
            _entry(card, var, show=show).pack(fill="x", pady=(2, 10))
            return var

        self._id_var = field("Voter ID")
        self._pw_var = field("Password", show="•")

        self._status = tk.Label(self, text="", bg=BG, fg=DANGER,
                                font=("Segoe UI", 9))
        self._status.pack(pady=4)

        _button(self, "Login", self._login).pack(fill="x", padx=40, pady=(4, 4))
        _button(self, "Register as New Voter", self._open_register,
                bg=SURFACE2, fg=FG).pack(fill="x", padx=40, pady=4)

        tk.Label(self, text="Default admin:  admin / Admin@1234",
                 bg=BG, fg=FG_DIM, font=("Segoe UI", 8)).pack(pady=(12, 0))

    def _login(self):
        vid = self._id_var.get().strip()
        pw  = self._pw_var.get()
        if not vid or not pw:
            self._status.config(text="Please fill in all fields")
            return
        if not self._rl.is_allowed(vid):
            self._status.config(text="Too many attempts. Please wait.")
            return
        voter = self._db.authenticate(vid, pw)
        if not voter:
            self._status.config(text="Invalid Voter ID or password")
            return
        self.destroy()
        if voter["is_admin"]:
            AdminDashboard(voter, self._db, self._nonce).mainloop()
        else:
            VoterDashboard(voter, self._db, self._nonce).mainloop()

    def _open_register(self):
        RegisterScreen(self, self._db)




class RegisterScreen(tk.Toplevel):

    def __init__(self, parent, db: VotingDatabase):
        super().__init__(parent)
        self._db = db
        self.title("Register")
        self.geometry("380x360")
        self.resizable(False, False)
        self.configure(bg=BG)
        self.grab_set()
        self._build_ui()

    def _build_ui(self):
        tk.Label(self, text="Register New Voter",
                 bg=BG, fg=ACCENT,
                 font=("Segoe UI", 13, "bold")).pack(pady=(20, 12))

        card = _card(self)
        card.pack(fill="x", padx=32)

        def field(label, show=""):
            tk.Label(card, text=label, bg=SURFACE, fg=FG_DIM,
                     font=("Segoe UI", 9)).pack(anchor="w")
            var = tk.StringVar()
            _entry(card, var, show=show).pack(fill="x", pady=(2, 8))
            return var

        self._name_var = field("Full Name")
        self._id_var   = field("Choose a Voter ID (min 4 chars)")
        self._pw_var   = field("Password (min 8 chars)", show="•")
        self._pw2_var  = field("Confirm Password", show="•")

        self._status = tk.Label(self, text="", bg=BG, fg=DANGER,
                                font=("Segoe UI", 9))
        self._status.pack()
        _button(self, "Register", self._submit).pack(fill="x", padx=32, pady=8)

    def _submit(self):
        name = self._name_var.get().strip()
        vid  = self._id_var.get().strip()
        pw   = self._pw_var.get()
        pw2  = self._pw2_var.get()
        if not all([name, vid, pw, pw2]):
            self._status.config(text="All fields required")
            return
        if pw != pw2:
            self._status.config(text="Passwords do not match")
            return
        try:
            ok = self._db.register_voter(vid, pw, name)
        except ValueError as e:
            self._status.config(text=str(e))
            return
        if not ok:
            self._status.config(text="Voter ID already taken")
            return
        messagebox.showinfo("Success", f"Account created!\nVoter ID: {vid}")
        self.destroy()




class BaseDashboard(tk.Tk):

    def __init__(self, voter, db, nonce):
        super().__init__()
        self._voter = voter
        self._db    = db
        self._nonce = nonce
        self.configure(bg=BG)
        self.protocol("WM_DELETE_WINDOW", self.destroy)

    def _header(self, title: str, subtitle: str = ""):
        f = tk.Frame(self, bg=SURFACE, pady=12, padx=20)
        f.pack(fill="x")
        tk.Label(f, text=title, bg=SURFACE, fg=ACCENT,
                 font=("Segoe UI", 14, "bold")).pack(side="left")
        tk.Label(f, text=subtitle, bg=SURFACE, fg=FG_DIM,
                 font=("Segoe UI", 9)).pack(side="right")

    def _clear_content(self):
        for w in self._content.winfo_children():
            w.destroy()

    def _logout(self):
        self.destroy()
        LoginScreen().mainloop()




class VoterDashboard(BaseDashboard):

    def __init__(self, voter, db, nonce):
        super().__init__(voter, db, nonce)
        self.title(f"Voting System – {voter['full_name']}")
        self.geometry("860x600")
        self.minsize(700, 500)
        self._build_ui()
        self._show_elections()

    def _build_ui(self):
        self._header("🗳  Secure Voting System",
                     f"Logged in as: {self._voter['full_name']}")
        nav = tk.Frame(self, bg=SURFACE, width=180)
        nav.pack(side="left", fill="y")
        nav.pack_propagate(False)
        for label, cmd in [("🗳  Open Elections", self._show_elections),
                            ("📊  Results",        self._show_results),
                            ("🚪  Logout",         self._logout)]:
            tk.Button(nav, text=label, command=cmd, bg=SURFACE, fg=FG,
                      font=("Segoe UI", 10), relief="flat", anchor="w",
                      cursor="hand2", activebackground=SURFACE2).pack(
                fill="x", padx=8, pady=3, ipady=6)
        self._content = tk.Frame(self, bg=BG, padx=20, pady=16)
        self._content.pack(side="right", fill="both", expand=True)

    def _show_elections(self):
        self._clear_content()
        _section_title(self._content, "Open Elections")
        elections = self._db.list_elections(status="open")
        if not elections:
            _label(self._content, "No elections are currently open.",
                   fg=FG_DIM).pack(anchor="w")
            return
        for e in elections:
            card = _card(self._content, padx=16, pady=10)
            card.pack(fill="x", pady=6)
            tk.Label(card, text=e["title"], bg=SURFACE, fg=FG,
                     font=("Segoe UI", 11, "bold")).pack(anchor="w")
            voted = self._db.has_voted(self._voter["voter_id"], e["id"])
            if voted:
                tk.Label(card, text="✔ You have already voted",
                         bg=SURFACE, fg=ACCENT2,
                         font=("Segoe UI", 9)).pack(anchor="w", pady=2)
            else:
                _button(card, "Cast Vote",
                        lambda eid=e["id"]: self._open_vote(eid)).pack(
                    anchor="w", pady=4)

    def _open_vote(self, election_id: int):
        self._clear_content()
        election = self._db.get_election(election_id)
        _section_title(self._content, f"🗳  {election['title']}")
        _label(self._content, "Select a candidate and click Submit Vote.",
               fg=FG_DIM).pack(anchor="w", pady=(0, 12))

        selected = tk.StringVar()
        for cand in election["candidates"]:
            f = tk.Frame(self._content, bg=SURFACE, padx=12, pady=8)
            f.pack(fill="x", pady=3)
            tk.Radiobutton(f, text=cand, variable=selected, value=cand,
                           bg=SURFACE, fg=FG, selectcolor=SURFACE2,
                           activebackground=SURFACE,
                           font=("Segoe UI", 11)).pack(anchor="w")

        status = tk.Label(self._content, text="", bg=BG, fg=DANGER,
                          font=("Segoe UI", 9))
        status.pack(anchor="w", pady=4)

        def submit():
            cand = selected.get()
            if not cand:
                status.config(text="Please select a candidate first.")
                return
            if not messagebox.askyesno(
                "Confirm Vote",
                f"You are about to vote for:\n\n  {cand}\n\n"
                "This cannot be undone. Proceed?"):
                return
            nonce = self._nonce.generate()
            if not self._nonce.is_fresh(nonce, time.time()):
                status.config(text="Security check failed. Try again.")
                return
            ok = self._db.cast_vote(self._voter["voter_id"],
                                    election_id, cand, nonce)
            if ok:
                messagebox.showinfo("Vote Cast",
                                    f"Your vote for '{cand}' has been recorded.\n"
                                    "It is encrypted and cannot be traced back to you.")
                self._show_elections()
            else:
                status.config(text="You have already voted in this election.")

        _button(self._content, "Submit Vote ✔", submit, bg=ACCENT2).pack(
            anchor="w", pady=8)
        _button(self._content, "← Back", self._show_elections,
                bg=SURFACE2, fg=FG).pack(anchor="w")

    def _show_results(self):
        self._clear_content()
        _section_title(self._content, "Election Results")
        elections = self._db.list_elections(status="closed")
        if not elections:
            _label(self._content, "No closed elections yet.",
                   fg=FG_DIM).pack(anchor="w")
            return
        for e in elections:
            card = _card(self._content, padx=16, pady=12)
            card.pack(fill="x", pady=6)
            tk.Label(card, text=e["title"], bg=SURFACE, fg=FG,
                     font=("Segoe UI", 11, "bold")).pack(anchor="w")
            _button(card, "View Results",
                    lambda eid=e["id"], et=e["title"]: self._show_tally(eid, et),
                    bg=SURFACE2, fg=FG).pack(anchor="w", pady=4)

    def _show_tally(self, election_id: int, title: str):
        self._clear_content()
        _section_title(self._content, f"Results: {title}")
        tally    = self._db.tally_votes(election_id)
        total    = sum(tally.values())
        winner   = max(tally, key=tally.get) if tally else None
        tally_ll = VoteTallyList()
        election = self._db.get_election(election_id)
        for c in election["candidates"]:
            tally_ll.add_candidate(c, c)
        for c, n in tally.items():
            for _ in range(n):
                tally_ll.record_vote(c)
        tally_ll.sort_by_votes()
        for node in tally_ll:
            pct = (node.count / total * 100) if total else 0
            row = tk.Frame(self._content, bg=SURFACE, padx=12, pady=8)
            row.pack(fill="x", pady=3)
            crown = "🏆 " if node.name == winner else "   "
            tk.Label(row, text=f"{crown}{node.name}",
                     bg=SURFACE,
                     fg=ACCENT2 if node.name == winner else FG,
                     font=("Segoe UI", 11, "bold")).pack(anchor="w")
            bar_f = tk.Frame(row, bg=SURFACE2, height=12)
            bar_f.pack(fill="x", pady=2)
            if pct > 0:
                tk.Frame(bar_f,
                         bg=ACCENT2 if node.name == winner else ACCENT,
                         height=12,
                         width=int(400 * pct / 100)).place(x=0, y=0)
            tk.Label(row, text=f"{node.count} votes ({pct:.1f}%)",
                     bg=SURFACE, fg=FG_DIM,
                     font=("Segoe UI", 9)).pack(anchor="w")
        tk.Label(self._content, text=f"Total votes cast: {total}",
                 bg=BG, fg=FG_DIM, font=("Segoe UI", 9)).pack(anchor="w", pady=8)
        _button(self._content, "← Back", self._show_results,
                bg=SURFACE2, fg=FG).pack(anchor="w")




class AdminDashboard(BaseDashboard):

    def __init__(self, voter, db, nonce):
        super().__init__(voter, db, nonce)
        self.title("Voting System – Admin Panel")
        self.geometry("960x640")
        self.minsize(750, 500)
        self._build_ui()
        self._show_manage()

    def _build_ui(self):
        self._header("⚙  Admin Dashboard",
                     f"Administrator: {self._voter['full_name']}")
        nav = tk.Frame(self, bg=SURFACE, width=200)
        nav.pack(side="left", fill="y")
        nav.pack_propagate(False)
        for label, cmd in [("📋  Manage Elections", self._show_manage),
                            ("➕  Create Election",  self._show_create),
                            ("📊  View Results",     self._show_results),
                            ("🔍  Audit Log",        self._show_audit),
                            ("🚪  Logout",           self._logout)]:
            tk.Button(nav, text=label, command=cmd, bg=SURFACE, fg=FG,
                      font=("Segoe UI", 10), relief="flat", anchor="w",
                      cursor="hand2", activebackground=SURFACE2).pack(
                fill="x", padx=8, pady=3, ipady=6)
        self._content = tk.Frame(self, bg=BG, padx=20, pady=16)
        self._content.pack(side="right", fill="both", expand=True)

    def _show_create(self):
        self._clear_content()
        _section_title(self._content, "Create New Election")
        card = _card(self._content)
        card.pack(fill="x")
        tk.Label(card, text="Election Title", bg=SURFACE, fg=FG_DIM,
                 font=("Segoe UI", 9)).pack(anchor="w")
        title_var = tk.StringVar()
        _entry(card, title_var, width=40).pack(fill="x", pady=(2, 10))
        tk.Label(card, text="Candidates (one per line, min 2)",
                 bg=SURFACE, fg=FG_DIM, font=("Segoe UI", 9)).pack(anchor="w")
        cand_box = tk.Text(card, height=6, bg=SURFACE2, fg=FG,
                           insertbackground=FG, relief="flat",
                           font=("Segoe UI", 11))
        cand_box.pack(fill="x", pady=(2, 10))
        status = tk.Label(self._content, text="", bg=BG, fg=DANGER,
                          font=("Segoe UI", 9))
        status.pack(anchor="w", pady=4)

        def create():
            title = title_var.get().strip()
            cands = [c.strip() for c in
                     cand_box.get("1.0", "end").splitlines() if c.strip()]
            if not title:
                status.config(text="Title is required"); return
            if len(cands) < 2:
                status.config(text="At least 2 candidates required"); return
            if len(cands) != len(set(cands)):
                status.config(text="Duplicate candidate names"); return
            try:
                eid = self._db.create_election(title, cands,
                                               self._voter["voter_id"])
                messagebox.showinfo("Created",
                                    f"Election #{eid} '{title}' created!")
                self._show_manage()
            except ValueError as e:
                status.config(text=str(e))

        _button(card, "Create Election", create, bg=ACCENT2).pack(
            anchor="w", pady=4)

    def _show_manage(self):
        self._clear_content()
        _section_title(self._content, "Manage Elections")
        elections = self._db.list_elections()
        if not elections:
            _label(self._content, "No elections yet.", fg=FG_DIM).pack(anchor="w")
            return
        for e in elections:
            card = _card(self._content, padx=16, pady=10)
            card.pack(fill="x", pady=5)
            top = tk.Frame(card, bg=SURFACE)
            top.pack(fill="x")
            tk.Label(top, text=f"#{e['id']}  {e['title']}",
                     bg=SURFACE, fg=FG,
                     font=("Segoe UI", 11, "bold")).pack(side="left")
            col = ACCENT2 if e["status"] == "open" else FG_DIM
            tk.Label(top, text=e["status"].upper(), bg=SURFACE, fg=col,
                     font=("Segoe UI", 9, "bold")).pack(side="right")
            count = self._db.vote_count(e["id"])
            tk.Label(card,
                     text=f"Votes: {count}  |  Candidates: {', '.join(e['candidates'])}",
                     bg=SURFACE, fg=FG_DIM,
                     font=("Segoe UI", 9)).pack(anchor="w", pady=2)
            if e["status"] == "open":
                _button(card, "Close Election",
                        lambda eid=e["id"]: self._close_election(eid),
                        bg=DANGER).pack(anchor="w", pady=4)

    def _close_election(self, election_id: int):
        if messagebox.askyesno("Close Election",
                               "Close this election? No more votes can be cast."):
            self._db.close_election(election_id, self._voter["voter_id"])
            messagebox.showinfo("Closed", "Election closed successfully.")
            self._show_manage()

    def _show_results(self):
        self._clear_content()
        _section_title(self._content, "Election Results")
        elections = self._db.list_elections(status="closed")
        if not elections:
            _label(self._content, "No closed elections yet.",
                   fg=FG_DIM).pack(anchor="w")
            return
        for e in elections:
            card = _card(self._content, padx=16, pady=10)
            card.pack(fill="x", pady=5)
            tk.Label(card, text=e["title"], bg=SURFACE, fg=FG,
                     font=("Segoe UI", 11, "bold")).pack(anchor="w")
            btn_f = tk.Frame(card, bg=SURFACE)
            btn_f.pack(anchor="w")
            _button(btn_f, "View Tally",
                    lambda eid=e["id"], et=e["title"]: self._show_tally(eid, et),
                    bg=SURFACE2, fg=FG).pack(side="left", padx=(0, 6), pady=4)
            _button(btn_f, "Export JSON",
                    lambda eid=e["id"]: self._export(eid),
                    bg=ACCENT2).pack(side="left", pady=4)

    def _show_tally(self, election_id: int, title: str):
        self._clear_content()
        _section_title(self._content, f"Results: {title}")
        tally    = self._db.tally_votes(election_id)
        total    = sum(tally.values())
        winner   = max(tally, key=tally.get) if tally else None
        tally_ll = VoteTallyList()
        election = self._db.get_election(election_id)
        for c in election["candidates"]:
            tally_ll.add_candidate(c, c)
        for c, n in tally.items():
            for _ in range(n):
                tally_ll.record_vote(c)
        tally_ll.sort_by_votes()
        for node in tally_ll:
            pct = (node.count / total * 100) if total else 0
            row = tk.Frame(self._content, bg=SURFACE, padx=12, pady=8)
            row.pack(fill="x", pady=3)
            crown = "🏆 " if node.name == winner else "    "
            tk.Label(row, text=f"{crown}{node.name}",
                     bg=SURFACE,
                     fg=ACCENT2 if node.name == winner else FG,
                     font=("Segoe UI", 11, "bold")).pack(anchor="w")
            bar_f = tk.Frame(row, bg=SURFACE2, height=10)
            bar_f.pack(fill="x", pady=2)
            if pct > 0:
                tk.Frame(bar_f,
                         bg=ACCENT2 if node.name == winner else ACCENT,
                         height=10,
                         width=int(450 * pct / 100)).place(x=0, y=0)
            tk.Label(row, text=f"{node.count} votes ({pct:.1f}%)",
                     bg=SURFACE, fg=FG_DIM,
                     font=("Segoe UI", 9)).pack(anchor="w")
        tk.Label(self._content, text=f"Total ballots cast: {total}",
                 bg=BG, fg=FG_DIM,
                 font=("Segoe UI", 9, "italic")).pack(anchor="w", pady=8)
        _button(self._content, "← Back", self._show_results,
                bg=SURFACE2, fg=FG).pack(anchor="w")

    def _export(self, election_id: int):
        fp = filedialog.asksaveasfilename(
            defaultextension=".json", filetypes=[("JSON", "*.json")])
        if fp:
            self._db.export_results_json(election_id, fp)
            messagebox.showinfo("Exported", f"Results saved to:\n{fp}")

    def _show_audit(self):
        self._clear_content()
        _section_title(self._content, "Audit Log")
        _label(self._content,
               "Immutable record of all system events (newest first)",
               fg=FG_DIM, font=("Segoe UI", 9)).pack(anchor="w", pady=(0, 8))

        cols = ("timestamp", "event", "actor", "detail")
        tree = ttk.Treeview(self._content, columns=cols,
                            show="headings", height=18)
        tree.heading("timestamp", text="Time")
        tree.heading("event",     text="Event")
        tree.heading("actor",     text="Actor")
        tree.heading("detail",    text="Detail")
        tree.column("timestamp", width=140, stretch=False)
        tree.column("event",     width=160, stretch=False)
        tree.column("actor",     width=100, stretch=False)
        tree.column("detail",    width=320)

        style = ttk.Style()
        style.configure("Treeview", background=SURFACE, foreground=FG,
                        fieldbackground=SURFACE, rowheight=22,
                        font=("Consolas", 9))
        style.configure("Treeview.Heading", background=BG, foreground=ACCENT,
                        font=("Segoe UI", 9, "bold"))

        audit_stack = AuditStack()
        for entry in self._db.get_audit_log(limit=200):
            audit_stack.push(entry)

        for entry in audit_stack.to_list():
            ts = time.strftime("%Y-%m-%d %H:%M:%S",
                               time.localtime(entry["timestamp"]))
            tree.insert("", "end",
                        values=(ts, entry["event_type"],
                                entry.get("actor", ""),
                                entry.get("detail", "")))

        vsb = ttk.Scrollbar(self._content, orient="vertical",
                            command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")


if __name__ == "__main__":
    LoginScreen().mainloop()
