(** * Interface to the Unix system *)

(** Note: description of the interfaces are derived from OCaml's documentation:
    https://github.com/ocaml/ocaml/blob/trunk/otherlibs/unix/unix.mli *)

(* begin hide *)
From Coq Require Import
     ExtrOcamlIntConv.

From SimpleIO Require Import
     IO_Monad
     IO_Stdlib
     IO_Pervasives.
(* end hide *)

Module OUnix.

(** ** Basic file input/output  *)

(** The abstract type of file descriptors. *)
Parameter file_descr : Set.

(** Close a file descriptor. *)
Parameter close : file_descr -> IO unit.

(** ** Time functions *)
Parameter sleep : int -> IO unit.

(** ** Internet addresses  *)

(** The abstract type of Internet addresses.  *)
Parameter inet_addr  : Set.

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

Variant socket_float_option :=
  SO_RCVTIMEO    (* Timeout for input operations *)
| SO_SNDTIMEO.   (* Timeout for output operations *)

(** Return the current status of a floating-point socket option. *)
Parameter getsockopt_float : OUnix.file_descr -> socket_float_option -> IO float.

(** Set a floating-point option in the given socket. *)
Parameter setsockopt_float : OUnix.file_descr -> socket_float_option -> float -> IO unit.

(* begin hide *)
Extract Inlined Constant file_descr         => "Unix.file_descr".
Extract Inlined Constant inet_addr          => "Unix.inet_addr".
Extract Inlined Constant inet_addr_any      => "Unix.inet_addr_any".
Extract Inlined Constant inet_addr_loopback => "Unix.inet_addr_loopback".

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
Extract Constant getsockopt_float => "fun f o   k -> k (Unix.getsockopt_float f o)".
Extract Constant setsockopt_float => "fun f o v k -> k (Unix.setsockopt_float f o v)".
(* end hide *)

End OUnix.
