include "ht.mm"
include "kl.mm"
include "tv.mm"
include "kc.mm"
include "wl.mm"
include "wv.mm"
include "wc.mm"
include "ke.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "beta.mm"
include "a1i.mm"
include "eqtypi.mm"
include "3eqtr4i.mm"
include "hb.mm"
include "kt.mm"
include "weq.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "hbov.mm"
include "weqi.mm"
include "id.mm"
include "ceq2.mm"
include "oveq12.mm"
include "eqid.mm"
include "ax-inst.mm"
include "leq.mm"
include "eta.mm"
include "3eqtr3i.mm"

theorem leqf
  param hal: type al
  param hbe: type be
  param vx: var x
  param vy: var y
  param ta: term A
  param tb: term B
  param tr: term R
  let vz: var z
  assume leqf.1: |- A : be
  assume leqf.2: |- R |= [ A = B ]
  assume leqf.3: |- T. |= [ ( \ x : al . R y : al ) = R ]

  disjoint A y
  disjoint B y
  disjoint R y
  disjoint x y
  disjoint al x
  disjoint al y
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint R z
  disjoint x z
  disjoint al z
  disjoint be z
  assert |- R |= [ \ x : al . A = \ x : al . B ]

  proof
    hal
    hbe
    ht
    hal
    vz
    hal
    vx
    ta
    kl
    #
    hal
    vz
    tv
    #
    kc
    #
    kl
    #
    hal
    vz
    hal
    vx
    tb
    kl
    #
    @1
    kc
    #
    kl
    #
    tr
    @0
    @4
    hal
    hbe
    vz
    @2
    hal
    hbe
    @0
    @1
    hal
    hbe
    vx
    ta
    leqf.1
    wl
    #
    hal
    vz
    wv
    #
    wc
    #
    wl
    hal
    hbe
    vz
    @2
    @5
    tr
    @9
    hal
    vx
    vy
    @0
    hal
    vx
    tv
    #
    kc
    #
    @4
    @10
    kc
    #
    ke
    kbr
    @2
    @5
    ke
    kbr
    @1
    tr
    tr
    hbe
    ta
    tb
    tr
    @11
    @12
    leqf.1
    leqf.2
    @11
    ta
    ke
    kbr
    tr
    ta
    tb
    ke
    kbr
    tr
    leqf.2
    ax-cb1
    #
    hal
    hbe
    vx
    ta
    leqf.1
    beta
    a1i
    @12
    tb
    ke
    kbr
    tr
    @13
    hal
    hbe
    vx
    tb
    hbe
    ta
    tb
    tr
    leqf.1
    leqf.2
    eqtypi
    #
    beta
    a1i
    3eqtr4i
    hal
    hbe
    hbe
    hb
    vx
    @2
    hal
    vy
    tv
    #
    @5
    ke
    kt
    hbe
    weq
    #
    @9
    hal
    vy
    wv
    #
    hal
    hbe
    @4
    @1
    hal
    hbe
    vx
    tb
    @14
    wl
    #
    @8
    wc
    hal
    hbe
    hbe
    hb
    ht
    ht
    vx
    ke
    @15
    @16
    @17
    ax-17
    hal
    hal
    hbe
    vx
    @1
    @15
    @0
    kt
    @7
    @8
    @17
    hal
    hal
    hbe
    vx
    ta
    @15
    leqf.1
    @17
    ax-hbl1
    hal
    hal
    vx
    @1
    @15
    @8
    @17
    ax-17
    #
    hbc
    hal
    hal
    hbe
    vx
    @1
    @15
    @4
    kt
    @18
    @8
    @17
    hal
    hal
    hbe
    vx
    tb
    @15
    @14
    @17
    ax-hbl1
    @19
    hbc
    hbov
    leqf.3
    hbe
    hbe
    hb
    @11
    @12
    @2
    ke
    @10
    @1
    ke
    kbr
    #
    @5
    @16
    hal
    hbe
    @0
    @10
    @7
    hal
    vx
    wv
    #
    wc
    hal
    hbe
    @4
    @10
    @18
    @21
    wc
    hal
    hbe
    @10
    @1
    @0
    @20
    @7
    @21
    @20
    hal
    @10
    @1
    @21
    @8
    weqi
    #
    id
    #
    ceq2
    hal
    hbe
    @10
    @1
    @4
    @20
    @18
    @21
    @23
    ceq2
    oveq12
    hb
    tr
    @20
    @22
    @13
    eqid
    ax-inst
    leq
    @3
    @0
    ke
    kbr
    tr
    @13
    hal
    hbe
    vz
    @0
    @7
    eta
    a1i
    @6
    @4
    ke
    kbr
    tr
    @13
    hal
    hbe
    vz
    @4
    @18
    eta
    a1i
    3eqtr3i
end
