(**
   [EasyLib] reexports [Lib] plus some additional features
   assuming Coq strings are extracted using [ExtrOcamlString]:

   - [ascii] is extracted to [char];
   - [string] is extracted to [char list].

   Though convenient, this is kept separate from [Lib] to limit
   the extraction hacks used by default.
 *)

From SimpleIO Require Export
     Lib CoqPervasives OcamlString.
