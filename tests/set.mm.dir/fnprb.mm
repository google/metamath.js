include "cpr.mm"
include "wfn.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wb.mm"
include "csn.mm"
include "fnsnb.mm"
include "dfsn2.mm"
include "fneq2i.mm"
include "eqeq2i.mm"
include "3bitr3i.mm"
include "a1i.mm"
include "preq2.mm"
include "fneq2d.mm"
include "id.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "preq2d.mm"
include "eqeq2d.mm"
include "3bitr3d.mm"
include "wne.mm"
include "wa.mm"
include "cdm.mm"
include "cv.mm"
include "wral.mm"
include "fndm.mm"
include "fvex.mm"
include "dmprop.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "wcel.mm"
include "eleq2d.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "fvpr1.mm"
include "adantr.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "fvpr2.mm"
include "jaod.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "fnfun.mm"
include "funpr.mm"
include "eqfunfv.mm"
include "syl2anr.mm"
include "mpbir2and.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "fneq1.mm"
include "biimprd.mm"
include "mpan9.mm"
include "impbida.mm"
include "pm2.61ine.mm"

theorem fnprb
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  assume fnprb.a: |- A e. _V
  assume fnprb.b: |- B e. _V


  assert |- ( F Fn { A , B } <-> F = { <. A , ( F ` A ) >. , <. B , ( F ` B ) >. } )

  proof
    cF
    cA
    cB
    cpr
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
    cpr
    #
    wceq
    #
    wb
    cA
    cB
    cA
    cB
    wceq
    #
    cF
    cA
    cA
    cpr
    #
    wfn
    #
    cF
    @3
    @3
    cpr
    #
    wceq
    #
    @1
    @7
    @10
    @12
    wb
    @8
    cF
    cA
    csn
    #
    wfn
    cF
    @3
    csn
    #
    wceq
    @10
    @12
    cA
    cF
    fnprb.a
    fnsnb
    @13
    @9
    cF
    cA
    dfsn2
    fneq2i
    @14
    @11
    cF
    @3
    dfsn2
    eqeq2i
    3bitr3i
    a1i
    @8
    @9
    @0
    cF
    cA
    cB
    cA
    preq2
    fneq2d
    @8
    @11
    @6
    cF
    @8
    @3
    @5
    @3
    @8
    cA
    cB
    @2
    @4
    @8
    id
    cA
    cB
    cF
    fveq2
    opeq12d
    preq2d
    eqeq2d
    3bitr3d
    cA
    cB
    wne
    #
    @1
    @7
    @15
    @1
    wa
    #
    @7
    cF
    cdm
    #
    @6
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
    @20
    @6
    cfv
    #
    wceq
    #
    vx
    @17
    wral
    #
    @1
    @19
    @15
    @1
    @17
    @0
    @18
    @0
    cF
    fndm
    #
    cA
    @2
    cB
    @4
    cA
    cF
    fvex
    #
    cB
    cF
    fvex
    #
    dmprop
    #
    syl6eqr
    adantl
    @16
    @23
    vx
    @17
    @16
    @20
    @17
    wcel
    @20
    @0
    wcel
    #
    @23
    @16
    @17
    @0
    @20
    @1
    @17
    @0
    wceq
    @15
    @25
    adantl
    eleq2d
    @29
    @20
    cA
    wceq
    #
    @20
    cB
    wceq
    #
    wo
    @16
    @23
    @20
    cA
    cB
    vx
    vex
    elpr
    @16
    @30
    @23
    @31
    @16
    @23
    @30
    @2
    cA
    @6
    cfv
    #
    wceq
    @16
    @32
    @2
    @15
    @32
    @2
    wceq
    @1
    cA
    cB
    @2
    @4
    fnprb.a
    @26
    fvpr1
    adantr
    eqcomd
    @30
    @21
    @2
    @22
    @32
    @20
    cA
    cF
    fveq2
    @20
    cA
    @6
    fveq2
    eqeq12d
    syl5ibrcom
    @16
    @23
    @31
    @4
    cB
    @6
    cfv
    #
    wceq
    @16
    @33
    @4
    @15
    @33
    @4
    wceq
    @1
    cA
    cB
    @2
    @4
    fnprb.b
    @27
    fvpr2
    adantr
    eqcomd
    @31
    @21
    @4
    @22
    @33
    @20
    cB
    cF
    fveq2
    @20
    cB
    @6
    fveq2
    eqeq12d
    syl5ibrcom
    jaod
    syl5bi
    sylbid
    ralrimiv
    @1
    cF
    wfun
    @6
    wfun
    #
    @7
    @19
    @24
    wa
    wb
    @15
    @0
    cF
    fnfun
    cA
    cB
    @2
    @4
    fnprb.a
    fnprb.b
    @26
    @27
    funpr
    #
    vx
    cF
    @6
    eqfunfv
    syl2anr
    mpbir2and
    @15
    @6
    @0
    wfn
    #
    @7
    @1
    @15
    @34
    @18
    @0
    wceq
    #
    @36
    @35
    @37
    @15
    @28
    a1i
    @6
    @0
    df-fn
    sylanbrc
    @7
    @1
    @36
    @0
    cF
    @6
    fneq1
    biimprd
    mpan9
    impbida
    pm2.61ine
end
