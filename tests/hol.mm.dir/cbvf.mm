include "ht.mm"
include "kl.mm"
include "tv.mm"
include "kc.mm"
include "kt.mm"
include "wl.mm"
include "wv.mm"
include "wc.mm"
include "ke.mm"
include "kbr.mm"
include "eqtypi.mm"
include "weqi.mm"
include "ax-17.mm"
include "clf.mm"
include "hb.mm"
include "weq.mm"
include "hbl.mm"
include "hbc.mm"
include "ax-cb1.mm"
include "hbl1.mm"
include "hbov.mm"
include "id.mm"
include "ceq2.mm"
include "beta.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtri.mm"
include "oveq12.mm"
include "insti.mm"
include "leq.mm"
include "eta.mm"
include "3eqtr3i.mm"

theorem cbvf
  param hal: type al
  param hbe: type be
  param vx: var x
  param vy: var y
  param vz: var z
  param ta: term A
  param tb: term B
  let vp: var p
  assume cbvf.1: |- A : be
  assume cbvf.2: |- T. |= [ ( \ y : al . A z : al ) = A ]
  assume cbvf.3: |- T. |= [ ( \ x : al . B z : al ) = B ]
  assume cbvf.4: |- [ x : al = y : al ] |= [ A = B ]

  disjoint A z
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint al x
  disjoint y z
  disjoint al y
  disjoint al z
  disjoint p z
  disjoint A p
  disjoint B p
  disjoint p x
  disjoint p y
  disjoint al p
  disjoint be p
  assert |- T. |= [ \ x : al . A = \ y : al . B ]

  proof
    hal
    hbe
    ht
    hal
    vp
    hal
    vx
    ta
    kl
    #
    hal
    vp
    tv
    #
    kc
    #
    kl
    hal
    vp
    hal
    vy
    tb
    kl
    #
    @1
    kc
    #
    kl
    kt
    @0
    @3
    hal
    hbe
    vp
    @2
    hal
    hbe
    @0
    @1
    hal
    hbe
    vx
    ta
    cbvf.1
    wl
    #
    hal
    vp
    wv
    #
    wc
    #
    wl
    hal
    hbe
    vp
    @2
    @4
    kt
    @7
    hal
    vy
    vz
    @0
    hal
    vy
    tv
    #
    kc
    #
    tb
    ke
    kbr
    @2
    @4
    ke
    kbr
    @1
    kt
    @6
    hbe
    @2
    @4
    @7
    hal
    hbe
    @3
    @1
    hal
    hbe
    vy
    tb
    hbe
    ta
    tb
    hal
    vx
    tv
    @8
    ke
    kbr
    cbvf.1
    cbvf.4
    eqtypi
    #
    wl
    #
    @6
    wc
    #
    weqi
    hal
    hbe
    vx
    vz
    ta
    tb
    @8
    cbvf.1
    hal
    vy
    wv
    #
    cbvf.4
    cbvf.3
    hal
    hal
    vx
    @8
    hal
    vz
    tv
    #
    @13
    hal
    vz
    wv
    #
    ax-17
    clf
    hal
    hbe
    hbe
    hb
    vy
    @2
    @14
    @4
    ke
    kt
    hbe
    weq
    #
    @7
    @15
    @12
    hal
    hbe
    hbe
    hb
    ht
    ht
    vy
    ke
    @14
    @16
    @15
    ax-17
    hal
    hal
    hbe
    vy
    @1
    @14
    @0
    kt
    @5
    @6
    @15
    hal
    hal
    hbe
    vy
    vx
    ta
    @14
    kt
    cbvf.1
    @15
    cbvf.2
    hbl
    hal
    hal
    vy
    @1
    @14
    @6
    @15
    ax-17
    #
    hbc
    hal
    hal
    hbe
    vy
    @1
    @14
    @3
    kt
    @11
    @6
    @15
    hal
    hal
    hbe
    vy
    tb
    @14
    kt
    @10
    @15
    hal
    vy
    ta
    kl
    @14
    kc
    ta
    ke
    kbr
    kt
    cbvf.2
    ax-cb1
    hbl1
    @17
    hbc
    hbov
    hbe
    hbe
    hb
    @9
    tb
    @2
    ke
    @8
    @1
    ke
    kbr
    #
    @4
    @16
    hal
    hbe
    @0
    @8
    @5
    @13
    wc
    @10
    hal
    hbe
    @8
    @1
    @0
    @18
    @5
    @13
    @18
    hal
    @8
    @1
    @13
    @6
    weqi
    id
    #
    ceq2
    #
    hbe
    tb
    @3
    @8
    kc
    #
    @4
    @18
    @10
    tb
    @21
    ke
    kbr
    @18
    @9
    @2
    ke
    kbr
    @18
    @20
    ax-cb1
    hbe
    @21
    tb
    kt
    hal
    hbe
    @3
    @8
    @11
    @13
    wc
    hal
    hbe
    vy
    tb
    @10
    beta
    eqcomi
    a1i
    hal
    hbe
    @8
    @1
    @3
    @18
    @11
    @13
    @19
    ceq2
    eqtri
    oveq12
    insti
    leq
    hal
    hbe
    vp
    @0
    @5
    eta
    hal
    hbe
    vp
    @3
    @11
    eta
    3eqtr3i
end
