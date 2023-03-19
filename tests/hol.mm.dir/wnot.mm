include "hb.mm"
include "ht.mm"
include "tv.mm"
include "tfal.mm"
include "tim.mm"
include "kbr.mm"
include "kl.mm"
include "tne.mm"
include "kt.mm"
include "wim.mm"
include "wv.mm"
include "wfal.mm"
include "wov.mm"
include "wl.mm"
include "df-not.mm"
include "eqtypri.mm"

theorem wnot
  let vf: var f
  let vp: var p
  let vq: var q
  let vx: var x
  let vy: var y


  assert |- ~ : ( bool -> bool )

  proof
    hb
    hb
    ht
    hb
    vp
    hb
    vp
    tv
    #
    tfal
    tim
    kbr
    #
    kl
    tne
    kt
    hb
    hb
    vp
    @1
    hb
    hb
    hb
    @0
    tfal
    tim
    wim
    hb
    vp
    wv
    wfal
    wov
    wl
    vp
    df-not
    eqtypri
end
