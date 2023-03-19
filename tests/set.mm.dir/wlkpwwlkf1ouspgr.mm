include "cuspgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "cwwlks.mm"
include "wf.mm"
include "wf1o.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "wbr.mm"
include "wex.mm"
include "fvex.mm"
include "breq1.mm"
include "spcev.mm"
include "wlkiswwlks.mm"
include "syl5ib.mm"
include "wlkcpr.mm"
include "biimpi.mm"
include "impel.mm"
include "fmptd.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "simpr.mm"
include "wb.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "fveq2.mm"
include "adantl.mm"
include "id.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "eqeqan12d.mm"
include "uspgr2wlkeqi.mm"
include "ad4ant134.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "wrex.mm"
include "adantr.mm"
include "cop.mm"
include "df-br.mm"
include "vex.mm"
include "op2nd.mm"
include "eqcomi.mm"
include "opex.mm"
include "eleq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "mpan2.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "syl6bir.mm"
include "imp.mm"
include "df-rex.mm"
include "sylibr.mm"
include "rexbiia.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "df-f1o.mm"
include "mpdan.mm"

theorem wlkpwwlkf1ouspgr
  let vw: setvar w
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume wlkpwwlkf1ouspgr.f: |- F = ( w e. ( Walks ` G ) |-> ( 2nd ` w ) )

  disjoint G w
  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint w x
  disjoint w y
  assert |- ( G e. USPGraph -> F : ( Walks ` G ) -1-1-onto-> ( WWalks ` G ) )

  proof
    cG
    cuspgr
    wcel
    #
    cG
    cwlks
    cfv
    #
    cG
    cwwlks
    cfv
    #
    cF
    wf
    #
    @1
    @2
    cF
    wf1o
    #
    @0
    vw
    @1
    vw
    cv
    #
    c2nd
    cfv
    #
    @2
    cF
    @0
    @5
    c1st
    cfv
    #
    @6
    @1
    wbr
    #
    @6
    @2
    wcel
    #
    @5
    @1
    wcel
    #
    @8
    vf
    cv
    #
    @6
    @1
    wbr
    #
    vf
    wex
    @0
    @9
    @12
    @8
    vf
    @7
    @5
    c1st
    fvex
    @11
    @7
    @6
    @1
    breq1
    spcev
    @6
    vf
    cG
    wlkiswwlks
    syl5ib
    @10
    @8
    cG
    @5
    wlkcpr
    biimpi
    impel
    wlkpwwlkf1ouspgr.f
    fmptd
    @0
    @3
    wa
    #
    @1
    @2
    cF
    wf1
    #
    @1
    @2
    cF
    wfo
    #
    @4
    @13
    @3
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    @14
    @0
    @3
    simpr
    #
    @13
    @22
    vx
    vy
    @1
    @1
    @13
    @16
    @1
    wcel
    #
    @18
    @1
    wcel
    #
    wa
    #
    wa
    #
    @20
    @16
    c2nd
    cfv
    #
    @18
    c2nd
    cfv
    #
    wceq
    #
    @21
    @26
    @20
    @30
    wb
    @13
    @24
    @25
    @17
    @28
    @19
    @29
    @24
    vw
    @16
    @6
    @28
    @1
    cF
    cvv
    cF
    vw
    @1
    @6
    cmpt
    wceq
    #
    @24
    wlkpwwlkf1ouspgr.f
    a1i
    vw
    vx
    weq
    @6
    @28
    wceq
    @24
    @5
    @16
    c2nd
    fveq2
    adantl
    @24
    id
    @24
    @16
    c2nd
    fvexd
    fvmptd
    #
    @25
    vw
    @18
    @6
    @29
    @1
    cF
    cvv
    @31
    @25
    wlkpwwlkf1ouspgr.f
    a1i
    vw
    vy
    weq
    @6
    @29
    wceq
    @25
    @5
    @18
    c2nd
    fveq2
    adantl
    @25
    id
    @25
    @18
    c2nd
    fvexd
    fvmptd
    eqeqan12d
    adantl
    @27
    @30
    @21
    @0
    @26
    @30
    @21
    @3
    @16
    @18
    cG
    uspgr2wlkeqi
    ad4ant134
    ex
    sylbid
    ralrimivva
    vx
    vy
    @1
    @2
    cF
    dff13
    sylanbrc
    @13
    @3
    @18
    @17
    wceq
    #
    vx
    @1
    wrex
    #
    vy
    @2
    wral
    @15
    @23
    @13
    @34
    vy
    @2
    @13
    @18
    @2
    wcel
    #
    wa
    #
    @18
    @28
    wceq
    #
    vx
    @1
    wrex
    #
    @34
    @36
    @24
    @37
    wa
    #
    vx
    wex
    #
    @38
    @13
    @35
    @40
    @13
    @35
    @11
    @18
    @1
    wbr
    #
    vf
    wex
    #
    @40
    @0
    @42
    @35
    wb
    @3
    @18
    vf
    cG
    wlkiswwlks
    adantr
    @41
    @40
    vf
    @41
    @11
    @18
    cop
    #
    @1
    wcel
    #
    @40
    @11
    @18
    @1
    df-br
    @44
    @18
    @43
    c2nd
    cfv
    #
    wceq
    #
    @40
    @45
    @18
    @11
    @18
    vf
    vex
    vy
    vex
    op2nd
    eqcomi
    @39
    @44
    @46
    wa
    vx
    @43
    @11
    @18
    opex
    @16
    @43
    wceq
    #
    @24
    @44
    @37
    @46
    @16
    @43
    @1
    eleq1
    @47
    @28
    @45
    @18
    @16
    @43
    c2nd
    fveq2
    eqeq2d
    anbi12d
    spcev
    mpan2
    sylbi
    exlimiv
    syl6bir
    imp
    @37
    vx
    @1
    df-rex
    sylibr
    @33
    @37
    vx
    @1
    @24
    @17
    @28
    @18
    @32
    eqeq2d
    rexbiia
    sylibr
    ralrimiva
    vx
    vy
    @1
    @2
    cF
    dffo3
    sylanbrc
    @1
    @2
    cF
    df-f1o
    sylanbrc
    mpdan
end
