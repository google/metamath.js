include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cfbas.mm"
include "cfv.mm"
include "wfn.mm"
include "cv.mm"
include "cfil.mm"
include "wral.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "cvv.mm"
include "cdm.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-fm.mm"
include "a1i.mm"
include "wa.mm"
include "dmeq.mm"
include "adantl.mm"
include "fdm.mm"
include "3ad2ant3.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "id.mm"
include "imaeq1.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "oveqan12d.mm"
include "mpteq12dv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "fex2.mm"
include "3com13.mm"
include "fvex.mm"
include "mptex.mm"
include "ovmpt2d.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl3.mm"
include "fmfil.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem fmf
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( X e. A /\ Y e. B /\ F : Y --> X ) -> ( X FilMap F ) : ( fBas ` Y ) --> ( Fil ` X ) )

  proof
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cX
    cF
    cfm
    co
    #
    cY
    cfbas
    cfv
    #
    wfn
    #
    vb
    cv
    #
    @4
    cfv
    cX
    cfil
    cfv
    #
    wcel
    #
    vb
    @5
    wral
    @5
    @8
    @4
    wf
    @3
    @6
    vb
    @5
    cX
    vy
    @7
    cF
    vy
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cmpt
    #
    @5
    wfn
    vb
    @5
    @14
    @15
    cX
    @13
    cfg
    ovex
    @15
    eqid
    fnmpti
    @3
    @5
    @4
    @15
    @3
    vx
    vf
    cX
    cF
    cvv
    cvv
    vb
    vf
    cv
    #
    cdm
    #
    cfbas
    cfv
    #
    vx
    cv
    #
    vy
    @7
    @16
    @10
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cmpt
    #
    @15
    cfm
    cvv
    cfm
    vx
    vf
    cvv
    cvv
    @24
    cmpt2
    wceq
    @3
    vx
    vb
    vy
    vf
    df-fm
    a1i
    @3
    @19
    cX
    wceq
    #
    @16
    cF
    wceq
    #
    wa
    #
    wa
    #
    vb
    @18
    @23
    @5
    @14
    @28
    @17
    cY
    cfbas
    @27
    @3
    @17
    cF
    cdm
    #
    cY
    @26
    @17
    @29
    wceq
    @25
    @16
    cF
    dmeq
    adantl
    @2
    @0
    @29
    cY
    wceq
    @1
    cY
    cX
    cF
    fdm
    3ad2ant3
    sylan9eqr
    fveq2d
    @27
    @23
    @14
    wceq
    @3
    @25
    @26
    @19
    cX
    @22
    @13
    cfg
    @25
    id
    @26
    @21
    @12
    @26
    vy
    @7
    @20
    @11
    @16
    cF
    @10
    imaeq1
    mpteq2dv
    rneqd
    oveqan12d
    adantl
    mpteq12dv
    @0
    @1
    cX
    cvv
    wcel
    @2
    cX
    cA
    elex
    3ad2ant1
    @2
    @1
    @0
    cF
    cvv
    wcel
    cY
    cX
    cF
    cB
    cA
    fex2
    3com13
    @15
    cvv
    wcel
    @3
    vb
    @5
    @14
    cY
    cfbas
    fvex
    mptex
    a1i
    ovmpt2d
    fneq1d
    mpbiri
    @3
    @9
    vb
    @5
    @3
    @7
    @5
    wcel
    #
    wa
    @0
    @30
    @2
    @9
    @0
    @1
    @2
    @30
    simpl1
    @3
    @30
    simpr
    @0
    @1
    @2
    @30
    simpl3
    cA
    @7
    cF
    cX
    cY
    fmfil
    syl3anc
    ralrimiva
    vb
    @5
    @8
    @4
    ffnfv
    sylanbrc
end
