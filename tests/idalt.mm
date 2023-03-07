      $c wff |- ( ) -> $.
      $v ph ps ch $.

      $( Let variable ph be a wff. $)
      wph $f wff ph $.

      $( Let variable ps be a wff. $)
      wps $f wff ps $.

      $( Let variable ch be a wff. $)
      wch $f wff ch $.

      wi $a wff ( ph -> ps ) $.

      ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
      ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

      ${
        min $e |- ph $.
        maj $e |- ( ph -> ps ) $.
        ax-mp $a |- ps $.
      $}

      $( [wph, wi, ax-1, ax-2, ax-mp] $)
      $( [wph, wph, wph, wi, *, wi, *, wph, wph, ax-1, wph, ...] $)
      idALT $p |- ( ph -> ph ) $=
        ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
