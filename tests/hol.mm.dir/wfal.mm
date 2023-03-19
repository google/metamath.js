include "hb.mm"
include "tal.mm"
include "tv.mm"
include "kl.mm"
include "kc.mm"
include "tfal.mm"
include "kt.mm"
include "ht.mm"
include "wal.mm"
include "wv.mm"
include "wl.mm"
include "wc.mm"
include "df-fal.mm"
include "eqtypri.mm"

theorem wfal
  let vf: var f
  let vp: var p
  let vq: var q
  let vx: var x
  let vy: var y


  assert |- F. : bool

  proof
    hb
    tal
    hb
    vp
    hb
    vp
    tv
    #
    kl
    #
    kc
    tfal
    kt
    hb
    hb
    ht
    hb
    tal
    @1
    hb
    wal
    hb
    hb
    vp
    @0
    hb
    vp
    wv
    wl
    wc
    vp
    df-fal
    eqtypri
end
