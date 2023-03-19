include "ctp.mm"
include "wfn.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wb.mm"
include "wne.mm"
include "wa.mm"
include "wi.mm"
include "cpr.mm"
include "fnprb.mm"
include "tpidm23.mm"
include "eqcomi.mm"
include "fneq2i.mm"
include "eqeq2i.mm"
include "3bitr3i.mm"
include "a1i.mm"
include "tpeq3.mm"
include "fneq2d.mm"
include "id.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "tpeq3d.mm"
include "eqeq2d.mm"
include "3bitr3d.mm"
include "a1d.mm"
include "cdm.mm"
include "cv.mm"
include "wral.mm"
include "fndm.mm"
include "fvex.mm"
include "dmtpop.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "wcel.mm"
include "eleq2d.mm"
include "w3o.mm"
include "vex.mm"
include "eltp.mm"
include "fvtp1.mm"
include "ad2antrr.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "fvtp2.mm"
include "ad4ant13.mm"
include "fvtp3.mm"
include "ad4ant23.mm"
include "3jaod.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "fnfun.mm"
include "funtp.mm"
include "3expa.mm"
include "eqfunfv.mm"
include "syl2anr.mm"
include "mpbir2and.mm"
include "fntp.mm"
include "fneq1.mm"
include "biimprd.mm"
include "mpan9.mm"
include "impbida.mm"
include "expcom.mm"
include "pm2.61ine.mm"
include "tpidm12.mm"
include "tpeq2.mm"
include "tpeq2d.mm"
include "tpidm13.mm"
include "pm2.61iine.mm"

theorem fntpb
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  assume fnprb.a: |- A e. _V
  assume fnprb.b: |- B e. _V
  assume fntpb.c: |- C e. _V


  assert |- ( F Fn { A , B , C } <-> F = { <. A , ( F ` A ) >. , <. B , ( F ` B ) >. , <. C , ( F ` C ) >. } )

  proof
    cF
    cA
    cB
    cC
    ctp
    #
    wfn
    #
    cF
    cA
    cA
    cF
    cfv
    #
    cop
    #
    cB
    cB
    cF
    cfv
    #
    cop
    #
    cC
    cC
    cF
    cfv
    #
    cop
    #
    ctp
    #
    wceq
    #
    wb
    #
    cA
    cA
    cB
    cC
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    wa
    #
    @10
    wi
    cB
    cC
    cB
    cC
    wceq
    #
    @10
    @13
    @14
    cF
    cA
    cB
    cB
    ctp
    #
    wfn
    #
    cF
    @3
    @5
    @5
    ctp
    #
    wceq
    #
    @1
    @9
    @16
    @18
    wb
    @14
    cF
    cA
    cB
    cpr
    #
    wfn
    #
    cF
    @3
    @5
    cpr
    #
    wceq
    #
    @16
    @18
    cA
    cB
    cF
    fnprb.a
    fnprb.b
    fnprb
    #
    @19
    @15
    cF
    @15
    @19
    cA
    cB
    tpidm23
    eqcomi
    fneq2i
    @21
    @17
    cF
    @17
    @21
    @3
    @5
    tpidm23
    eqcomi
    eqeq2i
    3bitr3i
    a1i
    @14
    @15
    @0
    cF
    cB
    cC
    cA
    cB
    tpeq3
    fneq2d
    @14
    @17
    @8
    cF
    @14
    @5
    @7
    @3
    @5
    @14
    cB
    cC
    @4
    @6
    @14
    id
    cB
    cC
    cF
    fveq2
    opeq12d
    tpeq3d
    eqeq2d
    3bitr3d
    a1d
    @13
    cB
    cC
    wne
    #
    @10
    @13
    @24
    wa
    #
    @1
    @9
    @25
    @1
    wa
    #
    @9
    cF
    cdm
    #
    @8
    cdm
    #
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    #
    @30
    @8
    cfv
    #
    wceq
    #
    vx
    @27
    wral
    #
    @1
    @29
    @25
    @1
    @27
    @0
    @28
    @0
    cF
    fndm
    #
    cA
    @2
    cB
    @4
    cC
    @6
    cA
    cF
    fvex
    #
    cB
    cF
    fvex
    #
    cC
    cF
    fvex
    #
    dmtpop
    syl6eqr
    adantl
    @26
    @33
    vx
    @27
    @26
    @30
    @27
    wcel
    @30
    @0
    wcel
    #
    @33
    @26
    @27
    @0
    @30
    @1
    @27
    @0
    wceq
    @25
    @35
    adantl
    eleq2d
    @39
    @30
    cA
    wceq
    #
    @30
    cB
    wceq
    #
    @30
    cC
    wceq
    #
    w3o
    @26
    @33
    @30
    cA
    cB
    cC
    vx
    vex
    eltp
    @26
    @40
    @33
    @41
    @42
    @26
    @33
    @40
    @2
    cA
    @8
    cfv
    #
    wceq
    @26
    @43
    @2
    @13
    @43
    @2
    wceq
    @24
    @1
    cA
    cB
    cC
    @2
    @4
    @6
    fnprb.a
    @36
    fvtp1
    ad2antrr
    eqcomd
    @40
    @31
    @2
    @32
    @43
    @30
    cA
    cF
    fveq2
    @30
    cA
    @8
    fveq2
    eqeq12d
    syl5ibrcom
    @26
    @33
    @41
    @4
    cB
    @8
    cfv
    #
    wceq
    @26
    @44
    @4
    @11
    @24
    @44
    @4
    wceq
    @12
    @1
    cA
    cB
    cC
    @2
    @4
    @6
    fnprb.b
    @37
    fvtp2
    ad4ant13
    eqcomd
    @41
    @31
    @4
    @32
    @44
    @30
    cB
    cF
    fveq2
    @30
    cB
    @8
    fveq2
    eqeq12d
    syl5ibrcom
    @26
    @33
    @42
    @6
    cC
    @8
    cfv
    #
    wceq
    @26
    @45
    @6
    @12
    @24
    @45
    @6
    wceq
    @11
    @1
    cA
    cB
    cC
    @2
    @4
    @6
    fntpb.c
    @38
    fvtp3
    ad4ant23
    eqcomd
    @42
    @31
    @6
    @32
    @45
    @30
    cC
    cF
    fveq2
    @30
    cC
    @8
    fveq2
    eqeq12d
    syl5ibrcom
    3jaod
    syl5bi
    sylbid
    ralrimiv
    @1
    cF
    wfun
    @8
    wfun
    #
    @9
    @29
    @34
    wa
    wb
    @25
    @0
    cF
    fnfun
    @11
    @12
    @24
    @46
    cA
    cB
    cC
    @2
    @4
    @6
    fnprb.a
    fnprb.b
    fntpb.c
    @36
    @37
    @38
    funtp
    3expa
    vx
    cF
    @8
    eqfunfv
    syl2anr
    mpbir2and
    @25
    @8
    @0
    wfn
    #
    @9
    @1
    @11
    @12
    @24
    @47
    cA
    cB
    cC
    @2
    @4
    @6
    fnprb.a
    fnprb.b
    fntpb.c
    @36
    @37
    @38
    fntp
    3expa
    @9
    @1
    @47
    @0
    cF
    @8
    fneq1
    biimprd
    mpan9
    impbida
    expcom
    pm2.61ine
    cA
    cB
    wceq
    #
    cF
    cA
    cA
    cC
    ctp
    #
    wfn
    #
    cF
    @3
    @3
    @7
    ctp
    #
    wceq
    #
    @1
    @9
    @50
    @52
    wb
    @48
    cF
    cA
    cC
    cpr
    #
    wfn
    cF
    @3
    @7
    cpr
    #
    wceq
    @50
    @52
    cA
    cC
    cF
    fnprb.a
    fntpb.c
    fnprb
    @53
    @49
    cF
    @49
    @53
    cA
    cC
    tpidm12
    eqcomi
    fneq2i
    @54
    @51
    cF
    @51
    @54
    @3
    @7
    tpidm12
    eqcomi
    eqeq2i
    3bitr3i
    a1i
    @48
    @49
    @0
    cF
    cA
    cB
    cA
    cC
    tpeq2
    fneq2d
    @48
    @51
    @8
    cF
    @48
    @3
    @5
    @3
    @7
    @48
    cA
    cB
    @2
    @4
    @48
    id
    cA
    cB
    cF
    fveq2
    opeq12d
    tpeq2d
    eqeq2d
    3bitr3d
    cA
    cC
    wceq
    #
    cF
    cA
    cB
    cA
    ctp
    #
    wfn
    #
    cF
    @3
    @5
    @3
    ctp
    #
    wceq
    #
    @1
    @9
    @57
    @59
    wb
    @55
    @20
    @22
    @57
    @59
    @23
    @19
    @56
    cF
    @56
    @19
    cA
    cB
    tpidm13
    eqcomi
    fneq2i
    @21
    @58
    cF
    @58
    @21
    @3
    @5
    tpidm13
    eqcomi
    eqeq2i
    3bitr3i
    a1i
    @55
    @56
    @0
    cF
    cA
    cC
    cA
    cB
    tpeq3
    fneq2d
    @55
    @58
    @8
    cF
    @55
    @3
    @7
    @3
    @5
    @55
    cA
    cC
    @2
    @6
    @55
    id
    cA
    cC
    cF
    fveq2
    opeq12d
    tpeq3d
    eqeq2d
    3bitr3d
    pm2.61iine
end
