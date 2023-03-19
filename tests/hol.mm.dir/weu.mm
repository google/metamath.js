include "hb.mm"
include "ht.mm"
include "tex.mm"
include "tal.mm"
include "tv.mm"
include "kc.mm"
include "ke.mm"
include "kbr.mm"
include "kl.mm"
include "teu.mm"
include "kt.mm"
include "wex.mm"
include "wal.mm"
include "wv.mm"
include "wc.mm"
include "weqi.mm"
include "wl.mm"
include "df-eu.mm"
include "eqtypri.mm"

theorem weu
  param hal: type al
  let vf: var f
  let vp: var p
  let vq: var q
  let vx: var x
  let vy: var y


  assert |- ?! : ( ( al -> bool ) -> bool )

  proof
    hal
    hb
    ht
    #
    hb
    ht
    @0
    vp
    tex
    hal
    vy
    tal
    hal
    vx
    @0
    vp
    tv
    #
    hal
    vx
    tv
    #
    kc
    #
    @2
    hal
    vy
    tv
    #
    ke
    kbr
    #
    ke
    kbr
    #
    kl
    #
    kc
    #
    kl
    #
    kc
    #
    kl
    teu
    kt
    @0
    hb
    vp
    @10
    @0
    hb
    tex
    @9
    hal
    wex
    hal
    hb
    vy
    @8
    @0
    hb
    tal
    @7
    hal
    wal
    hal
    hb
    vx
    @6
    hb
    @3
    @5
    hal
    hb
    @1
    @2
    @0
    vp
    wv
    hal
    vx
    wv
    #
    wc
    hal
    @2
    @4
    @11
    hal
    vy
    wv
    weqi
    weqi
    wl
    wc
    wl
    wc
    wl
    hal
    vx
    vy
    vp
    df-eu
    eqtypri
end
