include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "wreu.mm"
include "renegcl.mm"
include "zmin.mm"
include "syl.mm"
include "wb.mm"
include "zre.mm"
include "leneg.mm"
include "sylan.mm"
include "ancoms.mm"
include "znegcl.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "lenegcon1.mm"
include "adantrr.mm"
include "sylan2.mm"
include "adantrl.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "syld.mm"
include "com13.mm"
include "ralrimdv.mm"
include "breq2.mm"
include "exbiri.mm"
include "impbid.mm"
include "anbi12d.mm"
include "reubidva.mm"
include "cc.mm"
include "zcn.mm"
include "negcon2.mm"
include "syl2an.mm"
include "reuhyp.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "reuxfr.mm"
include "syl6rbbr.mm"
include "mpbid.mm"

theorem zmax
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( A e. RR -> E! x e. ZZ ( x <_ A /\ A. y e. ZZ ( y <_ A -> y <_ x ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    vz
    cv
    #
    cle
    wbr
    #
    @1
    vw
    cv
    #
    cle
    wbr
    #
    @2
    @4
    cle
    wbr
    #
    wi
    #
    vw
    cz
    wral
    #
    wa
    #
    vz
    cz
    wreu
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vy
    cv
    #
    cA
    cle
    wbr
    #
    @13
    @11
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
    #
    @0
    @1
    cr
    wcel
    @10
    cA
    renegcl
    vz
    vw
    @1
    zmin
    syl
    @0
    @19
    @1
    @11
    cneg
    #
    cle
    wbr
    #
    @5
    @20
    @4
    cle
    wbr
    #
    wi
    #
    vw
    cz
    wral
    #
    wa
    #
    vx
    cz
    wreu
    @10
    @0
    @18
    @25
    vx
    cz
    @0
    @11
    cz
    wcel
    #
    wa
    #
    @12
    @21
    @17
    @24
    @26
    @0
    @12
    @21
    wb
    #
    @26
    @11
    cr
    wcel
    #
    @0
    @28
    @11
    zre
    #
    @11
    cA
    leneg
    sylan
    ancoms
    @27
    @17
    @24
    @27
    @17
    @23
    vw
    cz
    @4
    cz
    wcel
    #
    @17
    @27
    @23
    @31
    @17
    @4
    cneg
    #
    cA
    cle
    wbr
    #
    @32
    @11
    cle
    wbr
    #
    wi
    #
    @27
    @23
    wi
    @31
    @32
    cz
    wcel
    @17
    @35
    wi
    @4
    znegcl
    @16
    @35
    vy
    @32
    cz
    @13
    @32
    wceq
    @14
    @33
    @15
    @34
    @13
    @32
    cA
    cle
    breq1
    @13
    @32
    @11
    cle
    breq1
    imbi12d
    rspcv
    syl
    @31
    @27
    @35
    @23
    @31
    @27
    @35
    @23
    wi
    @31
    @27
    wa
    @35
    @23
    @31
    @4
    cr
    wcel
    #
    @27
    @35
    @23
    wb
    @4
    zre
    @36
    @27
    wa
    @33
    @5
    @34
    @22
    @36
    @0
    @33
    @5
    wb
    @26
    @4
    cA
    lenegcon1
    adantrr
    @36
    @26
    @34
    @22
    wb
    #
    @0
    @26
    @36
    @29
    @37
    @30
    @4
    @11
    lenegcon1
    sylan2
    adantrl
    imbi12d
    sylan
    biimpd
    ex
    com23
    syld
    com13
    ralrimdv
    @27
    @24
    @16
    vy
    cz
    @13
    cz
    wcel
    #
    @24
    @27
    @16
    @38
    @24
    @1
    @13
    cneg
    #
    cle
    wbr
    #
    @20
    @39
    cle
    wbr
    #
    wi
    #
    @27
    @16
    wi
    @38
    @39
    cz
    wcel
    @24
    @42
    wi
    @13
    znegcl
    @23
    @42
    vw
    @39
    cz
    @4
    @39
    wceq
    @5
    @40
    @22
    @41
    @4
    @39
    @1
    cle
    breq2
    @4
    @39
    @20
    cle
    breq2
    imbi12d
    rspcv
    syl
    @38
    @27
    @42
    @16
    @38
    @27
    @16
    @42
    @38
    @13
    cr
    wcel
    #
    @27
    @16
    @42
    wb
    @13
    zre
    @43
    @27
    wa
    @14
    @40
    @15
    @41
    @43
    @0
    @14
    @40
    wb
    @26
    @13
    cA
    leneg
    adantrr
    @43
    @26
    @15
    @41
    wb
    #
    @0
    @26
    @43
    @29
    @44
    @30
    @13
    @11
    leneg
    sylan2
    adantrl
    imbi12d
    sylan
    exbiri
    com23
    syld
    com13
    ralrimdv
    impbid
    anbi12d
    reubidva
    @9
    @25
    vz
    vx
    @20
    cz
    @11
    znegcl
    vz
    vx
    @20
    @2
    cneg
    #
    cz
    @2
    znegcl
    @2
    cz
    wcel
    @2
    cc
    wcel
    @11
    cc
    wcel
    @2
    @20
    wceq
    #
    @11
    @45
    wceq
    wb
    @26
    @2
    zcn
    @11
    zcn
    @2
    @11
    negcon2
    syl2an
    reuhyp
    @46
    @3
    @21
    @8
    @24
    @2
    @20
    @1
    cle
    breq2
    @46
    @7
    @23
    vw
    cz
    @46
    @6
    @22
    @5
    @2
    @20
    @4
    cle
    breq1
    imbi2d
    ralbidv
    anbi12d
    reuxfr
    syl6rbbr
    mpbid
end
