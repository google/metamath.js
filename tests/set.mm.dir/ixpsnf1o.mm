include "wcel.mm"
include "csn.mm"
include "cixp.mm"
include "cv.mm"
include "cxp.mm"
include "crn.mm"
include "cuni.mm"
include "cvv.mm"
include "wa.mm"
include "snex.mm"
include "xpex.mm"
include "a1i.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "wceq.mm"
include "cop.mm"
include "wrex.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "wb.mm"
include "elixpsn.mm"
include "ax-mp.mm"
include "ixpeq1d.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "anbi1d.mm"
include "xpsn.mm"
include "eqeq2i.mm"
include "anbi2i.mm"
include "eqid.mm"
include "weq.mm"
include "opeq2.mm"
include "sneqd.mm"
include "rspcev.mm"
include "mpan2.mm"
include "op2nda.mm"
include "eqcomi.mm"
include "jctir.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rneq.mm"
include "unieqd.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wi.mm"
include "eqidd.mm"
include "ancli.mm"
include "eleq1.mm"
include "syl5bi.mm"
include "imbi12d.mm"
include "rexlimiv.mm"
include "impbii.mm"
include "bitri.mm"
include "vtoclbg.mm"
include "f1od.mm"

theorem ixpsnf1o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cI: class I
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cW: class W
  assume ixpsnf1o.f: |- F = ( x e. A |-> ( { I } X. { x } ) )

  disjoint I x
  disjoint I y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint V x
  disjoint V y
  disjoint F y
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W x
  disjoint W y
  assert |- ( I e. V -> F : A -1-1-onto-> X_ y e. { I } A )

  proof
    cI
    cV
    wcel
    #
    vx
    va
    cA
    vy
    cI
    csn
    #
    cA
    cixp
    #
    @1
    vx
    cv
    #
    csn
    #
    cxp
    #
    va
    cv
    #
    crn
    #
    cuni
    #
    cF
    cvv
    cvv
    ixpsnf1o.f
    @5
    cvv
    wcel
    @0
    @3
    cA
    wcel
    #
    wa
    @1
    @4
    cI
    snex
    @3
    snex
    xpex
    a1i
    @8
    cvv
    wcel
    @0
    @6
    @2
    wcel
    #
    wa
    @7
    @6
    va
    vex
    rnex
    uniex
    a1i
    @9
    @6
    vb
    cv
    #
    csn
    #
    @4
    cxp
    #
    wceq
    #
    wa
    #
    @6
    @11
    vc
    cv
    #
    cop
    #
    csn
    #
    wceq
    #
    vc
    cA
    wrex
    #
    @3
    @8
    wceq
    #
    wa
    #
    @9
    @6
    @5
    wceq
    #
    wa
    @10
    @21
    wa
    vb
    cI
    cV
    @11
    cI
    wceq
    #
    @14
    @23
    @9
    @24
    @13
    @5
    @6
    @24
    @12
    @1
    @4
    @11
    cI
    sneq
    #
    xpeq1d
    eqeq2d
    anbi2d
    @24
    @20
    @10
    @21
    @20
    @6
    vy
    @12
    cA
    cixp
    #
    wcel
    #
    @24
    @10
    @11
    cvv
    wcel
    @27
    @20
    wb
    vb
    vex
    #
    vy
    vc
    @11
    cA
    @6
    cvv
    elixpsn
    ax-mp
    @24
    @26
    @2
    @6
    @24
    vy
    @12
    @1
    cA
    @25
    ixpeq1d
    eleq2d
    syl5bbr
    anbi1d
    @15
    @9
    @6
    @11
    @3
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    @22
    @14
    @31
    @9
    @13
    @30
    @6
    @11
    @3
    @28
    vx
    vex
    #
    xpsn
    eqeq2i
    anbi2i
    @32
    @22
    @9
    @31
    @22
    @9
    @22
    @31
    @30
    @18
    wceq
    #
    vc
    cA
    wrex
    #
    @3
    @30
    crn
    #
    cuni
    #
    wceq
    #
    wa
    @9
    @35
    @38
    @9
    @30
    @30
    wceq
    #
    @35
    @30
    eqid
    @34
    @39
    vc
    @3
    cA
    vc
    vx
    weq
    #
    @18
    @30
    @30
    @40
    @17
    @29
    @16
    @3
    @11
    opeq2
    sneqd
    eqeq2d
    rspcev
    mpan2
    @37
    @3
    @11
    @3
    @28
    @33
    op2nda
    eqcomi
    jctir
    @31
    @20
    @35
    @21
    @38
    @31
    @19
    @34
    vc
    cA
    @6
    @30
    @18
    eqeq1
    rexbidv
    @31
    @8
    @37
    @3
    @31
    @7
    @36
    @6
    @30
    rneq
    unieqd
    eqeq2d
    anbi12d
    syl5ibrcom
    imp
    @20
    @21
    @32
    @19
    @21
    @32
    wi
    #
    vc
    cA
    @16
    cA
    wcel
    #
    @41
    @19
    @3
    @18
    crn
    #
    cuni
    #
    wceq
    #
    @9
    @18
    @30
    wceq
    #
    wa
    #
    wi
    @45
    vx
    vc
    weq
    #
    @42
    @47
    @44
    @16
    @3
    @11
    @16
    @28
    vc
    vex
    op2nda
    eqeq2i
    @42
    @47
    @48
    @42
    @18
    @18
    wceq
    #
    wa
    @42
    @49
    @42
    @18
    eqidd
    ancli
    @48
    @9
    @42
    @46
    @49
    @3
    @16
    cA
    eleq1
    @48
    @30
    @18
    @18
    @48
    @29
    @17
    @3
    @16
    @11
    opeq2
    sneqd
    eqeq2d
    anbi12d
    syl5ibrcom
    syl5bi
    @19
    @21
    @45
    @32
    @47
    @19
    @8
    @44
    @3
    @19
    @7
    @43
    @6
    @18
    rneq
    unieqd
    eqeq2d
    @19
    @31
    @46
    @9
    @6
    @18
    @30
    eqeq1
    anbi2d
    imbi12d
    syl5ibrcom
    rexlimiv
    imp
    impbii
    bitri
    vtoclbg
    f1od
end
