(** * Interface to the Unix system *)

(** Note: descriptions of the interface are derived from OCaml's documentation:
    https://caml.inria.fr/pub/docs/manual-ocaml/libref/Unix.html *)

(* begin hide *)
From Coq Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Monad
     IO_Stdlib
     IO_Float.
(* end hide *)

Module OUnix.

(** ** Basic file input/output  *)

(** The abstract type of file descriptors. *)
Parameter file_descr : Set.

Parameter file_descr_eqb : file_descr -> file_descr -> bool.

(** Close a file descriptor. *)
Parameter close : file_descr -> IO unit.

(** ** Polling  *)
(** Wait until some input/output operations become possible on some channels.
   The three list arguments are, respectively, a set of descriptors to check for
   reading (first argument), for writing (second argument), or for exceptional
   conditions (third argument).
   The fourth argument is the maximal timeout, in seconds; a negative fourth
   argument means no timeout (unbounded wait).
   The result is composed of three sets of descriptors: those ready for reading
   (first component), ready for writing (second component), and over which an
   exceptional condition is pending (third component). *)
Parameter select : list file_descr -> list file_descr -> list file_descr -> float ->
                   IO (list file_descr * list file_descr * list file_descr).

(** ** Time functions *)
Parameter sleep : int -> IO unit.

(** ** Internet addresses  *)

(** The abstract type of Internet addresses.  *)
Parameter inet_addr  : Set.

(** Conversion from the printable representation of an Internet
    address to its internal representation.  The argument string
    consists of 4 numbers separated by periods ([XXX.YYY.ZZZ.TTT])
    for IPv4 addresses, and up to 8 numbers separated by colons
    for IPv6 addresses.
    @raise Failure when given a string that does not match these formats. *)
Parameter inet_addr_of_string : ocaml_string -> IO inet_addr.

(** Return the printable representation of the given Internet address.
    See [inet_addr_of_string] for a description of the
    printable representation. *)
Parameter string_of_inet_addr : inet_addr -> ocaml_string.

(** A special IPv4 address, for use only with [bind], representing all the
    Internet addresses that the host machine possesses. *)
Parameter inet_addr_any : inet_addr.

(** A special IPv4 address representing the host machine ([127.0.0.1]). *)
Parameter inet_addr_loopback : inet_addr.

(** ** Sockets  *)

(** The type of socket domains. Not all platforms support IPv6 sockets (type
    [PF_INET6]). Windows does not support [PF_UNIX]. *)
Variant socket_domain :=
  PF_UNIX                       (** Unix domain *)
| PF_INET                       (** Internet domain (IPv4) *)
| PF_INET6.                     (** Internet domain (IPv6) *)

(** The type of socket addresses. [ADDR_UNIX name] is a socket address in the
    Unix domain; [name] is a file name in the file system. [ADDR_INET addr port]
    is a socket address in the Internet domain; [addr] is the Internet address
    of the machine, and [port] is the port number. *)
Variant socket_type :=
  SOCK_STREAM                   (** Stream socket *)
| SOCK_DGRAM                    (** Datagram socket *)
| SOCK_RAW                      (** Raw socket *)
| SOCK_SEQPACKET.               (** Sequenced packets socket *)

(** The type of socket addresses. [ADDR_UNIX name] is a socket address in the
    Unix domain; [name] is a file name in the file system. [ADDR_INET addr port]
    is a socket address in the Internet domain; [addr] is the Internet address
    of the machine, and [port] is the port number. *)
Variant sockaddr :=
  ADDR_UNIX : ocaml_string    -> sockaddr
| ADDR_INET : inet_addr -> int -> sockaddr.

(** Create a new socket in the given domain, and with the given kind. The third
    argument is the protocol type; 0 selects the default protocol for that kind
    of sockets. *)
Parameter socket : socket_domain -> socket_type -> int -> IO file_descr.

(** Accept connections on the given socket. The returned descriptor is a socket
    connected to the client; the returned address is the address of the
    connecting client. *)
Parameter accept : file_descr -> IO (file_descr * sockaddr).

(** Bind a socket to an address. *)
Parameter bind : file_descr -> sockaddr -> IO unit.

(** Connect a socket to an address. *)
Parameter connect : file_descr -> sockaddr -> IO unit.

(** Set up a socket for receiving connection requests. The integer argument is
    the maximal number of pending requests. *)
Parameter listen : file_descr -> int -> IO unit.

(** The flags for [Unix.recvfrom] and [sendto]. *)
Variant msg_flag :=
  MSG_OOB
| MSG_DONTROUTE
| MSG_PEEK.

(** Receive data from a connected socket. *)
Parameter recv :
  file_descr -> bytes -> int -> int -> list msg_flag -> IO int.

(** Send data over a connected socket. *)
Parameter send : file_descr -> bytes -> int -> int -> list msg_flag -> IO int.

(** ** Socket options *)

(** The socket options that can be consulted with [IO_Unix.getsockopt]
    and modified with [IO_Unix.setsockopt].  These options have a boolean
    ([true]/[false]) value. *)
Variant socket_bool_option :=
  SO_DEBUG       (* Record debugging information *)
| SO_BROADCAST   (* Permit sending of broadcast messages *)
| SO_REUSEADDR   (* Allow reuse of local addresses for bind *)
| SO_KEEPALIVE   (* Keep connection active *)
| SO_DONTROUTE   (* Bypass the standard routing algorithms *)
| SO_OOBINLINE   (* Leave out-of-band data in line *)
| SO_ACCEPTCONN  (* Report whether socket listening is enabled *)
| TCP_NODELAY    (* Control the Nagle algorithm for TCP sockets *)
| IPV6_ONLY.     (* Forbid binding an IPv6 socket to an IPv4 address *)

Variant socket_float_option :=
  SO_RCVTIMEO    (* Timeout for input operations *)
| SO_SNDTIMEO.   (* Timeout for output operations *)

(** Return the current status of a boolean-valued option in the given socket. *)
Parameter getsockopt : file_descr -> socket_bool_option -> IO bool.

(** Set or clear a boolean-valued option in the given socket. *)
Parameter setsockopt : file_descr -> socket_bool_option -> bool -> IO unit.

(** Return the current status of a floating-point socket option. *)
Parameter getsockopt_float : OUnix.file_descr -> socket_float_option -> IO float.

(** Set a floating-point option in the given socket. *)
Parameter setsockopt_float : OUnix.file_descr -> socket_float_option -> float -> IO unit.

(** Simple measure of time based on [int] to set socket timeouts with
    [setsockopt_time]. *)
Inductive time :=
| Seconds : int -> time
| Microsec : int -> time
.

(** Convert [time] to seconds as a [float]. *)
Definition time_as_seconds (t : time) : float :=
  match t with
  | Seconds n => OFloat.of_int n
  | Microsec n => OFloat.micro (OFloat.of_int n)
  end.

(** Set a timeout option in the given socket. *)
Definition setsock_timeout : OUnix.file_descr -> socket_float_option -> time -> IO unit
  := fun sock opt t => setsockopt_float sock opt (time_as_seconds t).

(** The type of error codes.  Errors defined in the POSIX standard and additional
    errors from UNIX98 and BSD. All other errors are mapped to [EUNKNOWNERR]. *)
Inductive error :=
| E2BIG  (* Argument list too long *)
| EACCES  (* Permission denied *)
| EAGAIN  (* Resource temporarily unavailable; try again *)
| EBADF  (* Bad file descriptor *)
| EBUSY  (* Resource unavailable *)
| ECHILD  (* No child process *)
| EDEADLK  (* Resource deadlock would occur *)
| EDOM  (* Domain error for math functions, etc. *)
| EEXIST  (* File exists *)
| EFAULT  (* Bad address *)
| EFBIG  (* File too large *)
| EINTR  (* Function interrupted by signal *)
| EINVAL  (* Invalid argument *)
| EIO  (* Hardware I/O error *)
| EISDIR  (* Is a directory *)
| EMFILE  (* Too many open files by the process *)
| EMLINK  (* Too many links *)
| ENAMETOOLONG  (* Filename too long *)
| ENFILE  (* Too many open files in the system *)
| ENODEV  (* No such device *)
| ENOENT  (* No such file or directory *)
| ENOEXEC  (* Not an executable file *)
| ENOLCK  (* No locks available *)
| ENOMEM  (* Not enough memory *)
| ENOSPC  (* No space left on device *)
| ENOSYS  (* Function not supported *)
| ENOTDIR  (* Not a directory *)
| ENOTEMPTY  (* Directory not empty *)
| ENOTTY  (* Inappropriate I/O control operation *)
| ENXIO  (* No such device or address *)
| EPERM  (* Operation not permitted *)
| EPIPE  (* Broken pipe *)
| ERANGE  (* Result too large *)
| EROFS  (* Read-only file system *)
| ESPIPE  (* Invalid seek e.g. on a pipe *)
| ESRCH  (* No such process *)
| EXDEV  (* Invalid link *)
| EWOULDBLOCK  (* Operation would block *)
| EINPROGRESS  (* Operation now in progress *)
| EALREADY  (* Operation already in progress *)
| ENOTSOCK  (* Socket operation on non-socket *)
| EDESTADDRREQ  (* Destination address required *)
| EMSGSIZE  (* Message too long *)
| EPROTOTYPE  (* Protocol wrong type for socket *)
| ENOPROTOOPT  (* Protocol not available *)
| EPROTONOSUPPORT  (* Protocol not supported *)
| ESOCKTNOSUPPORT  (* Socket type not supported *)
| EOPNOTSUPP  (* Operation not supported on socket *)
| EPFNOSUPPORT  (* Protocol family not supported *)
| EAFNOSUPPORT  (* Address family not supported by protocol family *)
| EADDRINUSE  (* Address already in use *)
| EADDRNOTAVAIL  (* Can't assign requested address *)
| ENETDOWN  (* Network is down *)
| ENETUNREACH  (* Network is unreachable *)
| ENETRESET  (* Network dropped connection on reset *)
| ECONNABORTED  (* Software caused connection abort *)
| ECONNRESET  (* Connection reset by peer *)
| ENOBUFS  (* No buffer space available *)
| EISCONN  (* Socket is already connected *)
| ENOTCONN  (* Socket is not connected *)
| ESHUTDOWN  (* Can't send after socket shutdown *)
| ETOOMANYREFS  (* Too many references: can't splice *)
| ETIMEDOUT  (* Connection timed out *)
| ECONNREFUSED  (* Connection refused *)
| EHOSTDOWN  (* Host is down *)
| EHOSTUNREACH  (* No route to host *)
| ELOOP  (* Too many levels of symbolic links *)
| EOVERFLOW  (* File size or position not representable *)
| EUNKNOWNERR (code : int) (* Unknown error *)
.

(** Return a string describing the given error code. *)
Parameter error_message : error -> ocaml_string.

(** Catch a Unix error.

    The first component is the error code; the second component is the function
    name; the third component is the string parameter to the function, if it
    has one, or the empty string otherwise. *)
Parameter catch_error
  : forall {a}, IO a -> (error -> ocaml_string -> ocaml_string -> IO a) -> IO a.


(** Raise a Unix error. Useful to rethrow errors that can't be handled. *)
Parameter raise_error : forall {a}, error -> ocaml_string -> ocaml_string -> IO a.

(* begin hide *)
Extract Inlined Constant file_descr         => "Unix.file_descr".
Extract Inlined Constant file_descr_eqb     => "(=)".
Extract Inlined Constant inet_addr          => "Unix.inet_addr".
Extract Inlined Constant inet_addr_any      => "Unix.inet_addr_any".
Extract Inlined Constant inet_addr_loopback => "Unix.inet_addr_loopback".
Extract Inlined Constant string_of_inet_addr => "Unix.string_of_inet_addr".

Extract Inductive socket_domain => "Unix.socket_domain"
                                 ["Unix.PF_UNIX"
                                  "Unix.PF_INET"
                                  "Unix.PF_INET6"].
Extract Inductive socket_type   => "Unix.socket_type"
                                 ["Unix.SOCK_STREAM"
                                  "Unix.SOCK_DGRAM"
                                  "Unix.SOCK_RAW"
                                  "Unix.SOCK_SEQPACKET"].
Extract Inductive sockaddr      => "Unix.sockaddr"
                                 ["Unix.ADDR_UNIX"
                                  "Unix.ADDR_INET"].
Extract Inductive msg_flag      => "Unix.msg_flag"
                                 ["Unix.MSG_OOB"
                                  "Unix.MSG_DONTROUTE"
                                  "Unix.MSG_PEEK"].
Extract Inductive socket_bool_option => "Unix.socket_bool_option"
                                      ["Unix.SO_DEBUG"
                                       "Unix.SO_BROADCAST"
                                       "Unix.SO_REUSEADDR"
                                       "Unix.SO_KEEPALIVE"
                                       "Unix.SO_DONTROUTE"
                                       "Unix.OOBINLINE"
                                       "Unix.SO_ACCEPTCONN"
                                       "Unix.TCP_NODELAY"
                                       "Unix.IPV6_ONLY"].
Extract Inductive socket_float_option => "Unix.socket_float_option"
                                       ["Unix.SO_RCVTIMEO"
                                        "Unix.SO_SNDTIMEO"].

Extract Constant close  => "fun f           k -> k (Unix.close f)".
Extract Constant sleep  => "fun d           k -> k (Unix.sleep d)".
Extract Constant socket => "fun d t p       k -> k (Unix.socket d t p)".
Extract Constant accept => "fun f           k -> k (Unix.accept f)".
Extract Constant bind   => "fun f a         k -> k (Unix.bind f a)".
Extract Constant connect => "fun f a        k -> k (Unix.connect f a)".
Extract Constant listen => "fun f i         k -> k (Unix.listen f i)".
Extract Constant recv   => "fun f b o l g   k -> k (Unix.recv f b o l g)".
Extract Constant send   => "fun f b o l g   k -> k (Unix.send f b o l g)".
Extract Constant getsockopt =>       "fun f o   k -> k (Unix.getsockopt f o)".
Extract Constant setsockopt =>       "fun f o b k -> k (Unix.setsockopt f o b)".
Extract Constant getsockopt_float => "fun f o   k -> k (Unix.getsockopt_float f o)".
Extract Constant setsockopt_float => "fun f o v k -> k (Unix.setsockopt_float f o v)".
Extract Constant inet_addr_of_string => "fun  s k -> k (Unix.inet_addr_of_string s)".
Extract Constant select => "fun r w e t k ->
                             k (let (r',w',e') = Unix.select r w e t in
                                ((r',w'),e'))".

Extract Inductive error => "Unix.error"
[ "Unix.E2BIG"
  "Unix.EACCES"
  "Unix.EAGAIN"
  "Unix.EBADF"
  "Unix.EBUSY"
  "Unix.ECHILD"
  "Unix.EDEADLK"
  "Unix.EDOM"
  "Unix.EEXIST"
  "Unix.EFAULT"
  "Unix.EFBIG"
  "Unix.EINTR"
  "Unix.EINVAL"
  "Unix.EIO"
  "Unix.EISDIR"
  "Unix.EMFILE"
  "Unix.EMLINK"
  "Unix.ENAMETOOLONG"
  "Unix.ENFILE"
  "Unix.ENODEV"
  "Unix.ENOENT"
  "Unix.ENOEXEC"
  "Unix.ENOLCK"
  "Unix.ENOMEM"
  "Unix.ENOSPC"
  "Unix.ENOSYS"
  "Unix.ENOTDIR"
  "Unix.ENOTEMPTY"
  "Unix.ENOTTY"
  "Unix.ENXIO"
  "Unix.EPERM"
  "Unix.EPIPE"
  "Unix.ERANGE"
  "Unix.EROFS"
  "Unix.ESPIPE"
  "Unix.ESRCH"
  "Unix.EXDEV"
  "Unix.EWOULDBLOCK"
  "Unix.EINPROGRESS"
  "Unix.EALREADY"
  "Unix.ENOTSOCK"
  "Unix.EDESTADDRREQ"
  "Unix.EMSGSIZE"
  "Unix.EPROTOTYPE"
  "Unix.ENOPROTOOPT"
  "Unix.EPROTONOSUPPORT"
  "Unix.ESOCKTNOSUPPORT"
  "Unix.EOPNOTSUPP"
  "Unix.EPFNOSUPPORT"
  "Unix.EAFNOSUPPORT"
  "Unix.EADDRINUSE"
  "Unix.EADDRNOTAVAIL"
  "Unix.ENETDOWN"
  "Unix.ENETUNREACH"
  "Unix.ENETRESET"
  "Unix.ECONNABORTED"
  "Unix.ECONNRESET"
  "Unix.ENOBUFS"
  "Unix.EISCONN"
  "Unix.ENOTCONN"
  "Unix.ESHUTDOWN"
  "Unix.ETOOMANYREFS"
  "Unix.ETIMEDOUT"
  "Unix.ECONNREFUSED"
  "Unix.EHOSTDOWN"
  "Unix.EHOSTUNREACH"
  "Unix.ELOOP"
  "Unix.EOVERFLOW"
  "Unix.EUNKNOWNERR" ].

Extract Inlined Constant error_message => "Unix.error_message".

Extract Constant catch_error => "fun u h k ->
  match Obj.magic u (fun a -> a) with
  | exception Unix.Unix_error (e, fname, sparam) -> h e fname sparam k
  | a -> k a".

Extract Constant raise_error =>
  "fun e fname sparam _k -> raise (Unix.Unix_error (e, fname, sparam))".
(* end hide *)

End OUnix.
