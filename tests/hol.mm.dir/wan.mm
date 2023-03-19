include "hb.mm"
include "ht.mm"
include "tv.mm"
include "kbr.mm"
include "kl.mm"
include "kt.mm"
include "ke.mm"
include "tan.mm"
include "wv.mm"
include "wov.mm"
include "wl.mm"
include "wtru.mm"
include "weqi.mm"
include "df-an.mm"
include "eqtypri.mm"

theorem wan
  let vf: var f
  let vp: var p
  let vq: var q
  let vx: var x
  let vy: var y


  assert |- /\ : ( bool -> ( bool -> bool ) )

  proof
    hb
    hb
    hb
    ht
    #
    ht
    #
    hb
    vp
    hb
    vq
    @1
    vf
    hb
    vp
    tv
    #
    hb
    vq
    tv
    #
    @1
    vf
    tv
    #
    kbr
    #
    kl
    #
    @1
    vf
    kt
    kt
    @4
    kbr
    #
    kl
    #
    ke
    kbr
    #
    kl
    #
    kl
    tan
    kt
    hb
    @0
    vp
    @10
    hb
    hb
    vq
    @9
    @1
    hb
    ht
    @6
    @8
    @1
    hb
    vf
    @5
    hb
    hb
    hb
    @2
    @3
    @4
    @1
    vf
    wv
    #
    hb
    vp
    wv
    hb
    vq
    wv
    wov
    wl
    @1
    hb
    vf
    @7
    hb
    hb
    hb
    kt
    kt
    @4
    @11
    wtru
    wtru
    wov
    wl
    weqi
    wl
    wl
    vf
    vp
    vq
    df-an
    eqtypri
end
