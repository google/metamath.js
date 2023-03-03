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

      ${
        mpd.1 $e |- ( ph -> ps ) $.
        mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
        $(
          makes this an axiom as opposed to a theorem, so that we
          can skip bringing in the proof recursively.
          mpd $p |- ( ph -> ch ) $=
            ( wi a2i ax-mp ) ABFACFDABCEGH $.
        $)
        mpd $a |- ( ph -> ch ) $.
      $}

      $( 1 1 1 2 Z 1 1 1 3 1 5 3 4 $)
      $( mandatory: wph $)
      $( local: wi ax-1 mpd $)
      $( decompressed: wph wph wph wi (Z) wph wph wph ax-1 wph (Z: wph wph wph wi) ax-1 mpd $)
      $(
       wph, wph, wph  wi                  wph, wph, wph         ax-1                          wph


                                          wff ph                                              wff ph
                                          wff ph                |- ( ph -> ( ph -> ph ) )     |- ( ph -> ( ph -> ph ) )
       wff ph                             wff ph                wff ph                        wff ph
       wff ph         wff ( ph -> ph )    wff ( ph -> ph )      wff ( ph -> ph )              wff ( ph -> ph )
       wff ph         wff ph              wff ph                wff ph                        wff ph


       wi                               ax-1                                        mpd

                        
       wff ( ph -> ph )                 
       wff ph                           |- ( ph -> ( ( ph -> ph ) -> ph ) )         
       |- ( ph -> ( ph -> ph ) )        |- ( ph -> ( ph -> ph ) )
       wff ph                           wff ph
       wff ( ph -> ph )                 wff ( ph -> ph )
       wff ph                           wff ph                                      |- ( ph -> ph )
      $)
      id $p |- ( ph -> ph ) $=
        ( wi ax-1 mpd ) AAABZAAACAECD $.
