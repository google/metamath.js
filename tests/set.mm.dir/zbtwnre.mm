include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "wreu.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "zmin.mm"
include "wb.mm"
include "cmin.mm"
include "zre.mm"
include "peano2rem.mm"
include "syl.mm"
include "ltletr.mm"
include "syl3an1.mm"
include "3expa.mm"
include "sylan2.mm"
include "zlem1lt.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "exp4b.mm"
include "com23.mm"
include "ralrimdv.mm"
include "wn.mm"
include "ltnrd.mm"
include "peano2zm.mm"
include "mpdan.mm"
include "mtbird.mm"
include "ad2antrr.mm"
include "lenlt.mm"
include "ancoms.mm"
include "adantr.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "imp.mm"
include "sylbird.mm"
include "mt3d.mm"
include "ex.mm"
include "impbid.mm"
include "1re.mm"
include "ltsubadd.mm"
include "mp3an2.mm"
include "sylan.mm"
include "bitr3d.mm"
include "anbi2d.mm"
include "reubidva.mm"
include "mpbid.mm"

theorem zbtwnre
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. RR -> E! x e. ZZ ( A <_ x /\ x < ( A + 1 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    vx
    cv
    #
    cle
    wbr
    #
    cA
    vy
    cv
    #
    cle
    wbr
    #
    @1
    @3
    cle
    wbr
    #
    wi
    #
    vy
    cz
    wral
    #
    wa
    #
    vx
    cz
    wreu
    @2
    @1
    cA
    c1
    caddc
    co
    clt
    wbr
    #
    wa
    #
    vx
    cz
    wreu
    vx
    vy
    cA
    zmin
    @0
    @8
    @10
    vx
    cz
    @0
    @1
    cz
    wcel
    #
    wa
    @7
    @9
    @2
    @11
    @0
    @7
    @9
    wb
    @11
    @0
    wa
    #
    @1
    c1
    cmin
    co
    #
    cA
    clt
    wbr
    #
    @7
    @9
    @12
    @14
    @7
    @12
    @14
    @6
    vy
    cz
    @12
    @3
    cz
    wcel
    #
    @14
    @6
    @12
    @15
    @14
    @4
    @5
    @12
    @15
    wa
    @14
    @4
    wa
    #
    @13
    @3
    clt
    wbr
    #
    @5
    @15
    @12
    @3
    cr
    wcel
    #
    @16
    @17
    wi
    #
    @3
    zre
    @11
    @0
    @18
    @19
    @11
    @13
    cr
    wcel
    #
    @0
    @18
    @19
    @11
    @1
    cr
    wcel
    #
    @20
    @1
    zre
    #
    @1
    peano2rem
    syl
    #
    @13
    cA
    @3
    ltletr
    syl3an1
    3expa
    sylan2
    @11
    @15
    @5
    @17
    wb
    @0
    @1
    @3
    zlem1lt
    adantlr
    sylibrd
    exp4b
    com23
    ralrimdv
    @12
    @7
    @14
    @12
    @7
    wa
    #
    @14
    @1
    @13
    cle
    wbr
    #
    @11
    @25
    wn
    @0
    @7
    @11
    @25
    @13
    @13
    clt
    wbr
    #
    @11
    @13
    @23
    ltnrd
    @11
    @13
    cz
    wcel
    #
    @25
    @26
    wb
    @1
    peano2zm
    #
    @1
    @13
    zlem1lt
    mpdan
    mtbird
    ad2antrr
    @24
    @14
    wn
    #
    cA
    @13
    cle
    wbr
    #
    @25
    @12
    @30
    @29
    wb
    #
    @7
    @0
    @11
    @31
    @11
    @0
    @20
    @31
    @23
    cA
    @13
    lenlt
    sylan2
    ancoms
    adantr
    @11
    @7
    @30
    @25
    wi
    #
    @0
    @11
    @7
    @32
    @11
    @27
    @7
    @32
    wi
    @28
    @6
    @32
    vy
    @13
    cz
    @3
    @13
    wceq
    @4
    @30
    @5
    @25
    @3
    @13
    cA
    cle
    breq2
    @3
    @13
    @1
    cle
    breq2
    imbi12d
    rspcv
    syl
    imp
    adantlr
    sylbird
    mt3d
    ex
    impbid
    @11
    @21
    @0
    @14
    @9
    wb
    #
    @22
    @21
    c1
    cr
    wcel
    @0
    @33
    1re
    @1
    c1
    cA
    ltsubadd
    mp3an2
    sylan
    bitr3d
    ancoms
    anbi2d
    reubidva
    mpbid
end
