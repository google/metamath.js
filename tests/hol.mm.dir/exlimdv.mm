include "kl.mm"
include "hb.mm"
include "kct.mm"
include "ax-cb1.mm"
include "wctr.mm"
include "wl.mm"
include "tv.mm"
include "kc.mm"
include "wv.mm"
include "wc.mm"
include "ax-cb2.mm"
include "tim.mm"
include "kbr.mm"
include "wim.mm"
include "wov.mm"
include "ex.mm"
include "kt.mm"
include "ht.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "hbov.mm"
include "ke.mm"
include "weqi.mm"
include "beta.mm"
include "eqcomi.mm"
include "a1i.mm"
include "id.mm"
include "ceq2.mm"
include "eqtri.mm"
include "oveq1.mm"
include "insti.mm"
include "imp.mm"
include "exlimdv2.mm"

theorem exlimdv
  param hal: type al
  param vx: var x
  param ta: term A
  param tr: term R
  param tt: term T
  let vy: var y
  let vz: var z
  assume exlimdv.1: |- ( R , A ) |= T

  disjoint R x
  disjoint T x
  disjoint al x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint R y
  disjoint R z
  disjoint T y
  disjoint T z
  disjoint al y
  disjoint al z
  assert |- ( R , ( ? \ x : al . A ) ) |= T

  proof
    hal
    vy
    hal
    vx
    ta
    kl
    #
    tr
    tt
    hal
    hb
    vx
    ta
    tr
    ta
    tt
    tr
    ta
    kct
    #
    exlimdv.1
    ax-cb1
    wctr
    #
    wl
    #
    tr
    @0
    hal
    vy
    tv
    #
    kc
    #
    tt
    hal
    hb
    @0
    @4
    @3
    hal
    vy
    wv
    #
    wc
    #
    tt
    @1
    exlimdv.1
    ax-cb2
    #
    hal
    vx
    vz
    ta
    tt
    tim
    kbr
    @5
    tt
    tim
    kbr
    @4
    tr
    @6
    hb
    hb
    hb
    @5
    tt
    tim
    wim
    @7
    @8
    wov
    tr
    ta
    tt
    exlimdv.1
    ex
    hal
    hb
    hb
    hb
    vx
    @5
    hal
    vz
    tv
    #
    tt
    tim
    kt
    wim
    @7
    hal
    vz
    wv
    #
    @8
    hal
    hb
    hb
    hb
    ht
    ht
    vx
    tim
    @9
    wim
    @10
    ax-17
    hal
    hal
    hb
    vx
    @4
    @9
    @0
    kt
    @3
    @6
    @10
    hal
    hal
    hb
    vx
    ta
    @9
    @2
    @10
    ax-hbl1
    hal
    hal
    vx
    @4
    @9
    @6
    @10
    ax-17
    hbc
    hal
    hb
    vx
    tt
    @9
    @8
    @10
    ax-17
    hbov
    hb
    hb
    hb
    ta
    tt
    @5
    tim
    hal
    vx
    tv
    #
    @4
    ke
    kbr
    #
    wim
    @2
    @8
    hb
    ta
    @0
    @11
    kc
    #
    @5
    @12
    @2
    ta
    @13
    ke
    kbr
    @12
    hal
    @11
    @4
    hal
    vx
    wv
    #
    @6
    weqi
    #
    hb
    @13
    ta
    kt
    hal
    hb
    @0
    @11
    @3
    @14
    wc
    hal
    hb
    vx
    ta
    @2
    beta
    eqcomi
    a1i
    hal
    hb
    @11
    @4
    @0
    @12
    @3
    @14
    @12
    @15
    id
    ceq2
    eqtri
    oveq1
    insti
    imp
    exlimdv2
end
