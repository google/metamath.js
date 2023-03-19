include "kt.mm"
include "tex.mm"
include "kc.mm"
include "tat.mm"
include "tv.mm"
include "wv.mm"
include "ac.mm"
include "wtru.mm"
include "adantl.mm"
include "exlimdv2.mm"
include "hb.mm"
include "ht.mm"
include "wat.mm"
include "wc.mm"
include "ax4e.mm"
include "ded.mm"

theorem dfex2
  let hal: type al
  let tf: term F
  let vx: var x
  assume dfex2.1: |- F : ( al -> bool )


  assert |- T. |= [ ( ? F ) = ( F ( @ F ) ) ]

  proof
    kt
    tex
    tf
    kc
    #
    tf
    tat
    tf
    kc
    #
    kc
    #
    hal
    vx
    tf
    kt
    @2
    dfex2.1
    tf
    hal
    vx
    tv
    #
    kc
    kt
    @2
    hal
    @3
    tf
    dfex2.1
    hal
    vx
    wv
    ac
    wtru
    adantl
    exlimdv2
    @2
    kt
    @0
    hal
    @1
    tf
    dfex2.1
    hal
    hb
    ht
    hal
    tat
    tf
    hal
    wat
    dfex2.1
    wc
    ax4e
    wtru
    adantl
    ded
end
