include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cc.mm"
include "dvf.mm"
include "ffn.mm"
include "mp1i.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "ccj.mm"
include "ccom.mm"
include "wceq.mm"
include "simpr.mm"
include "fvco3.mm"
include "sylancr.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mpan2.mm"
include "dvcj.mm"
include "sylan.mm"
include "cmpt.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "cjred.mm"
include "mpteq2dva.mm"
include "recnd.mm"
include "simpl.mm"
include "feqmptd.mm"
include "cjf.mm"
include "a1i.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cjrebd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem dvfre
  let cA: class A
  let cF: class F
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N


  assert |- ( ( F : A --> RR /\ A C_ RR ) -> ( RR _D F ) : dom ( RR _D F ) --> RR )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cr
    wss
    #
    wa
    #
    cr
    cF
    cdv
    co
    #
    @3
    cdm
    #
    wfn
    #
    vx
    cv
    #
    @3
    cfv
    #
    cr
    wcel
    #
    vx
    @4
    wral
    @4
    cr
    @3
    wf
    @4
    cc
    @3
    wf
    #
    @5
    @2
    cF
    dvf
    #
    @4
    cc
    @3
    ffn
    mp1i
    @2
    @8
    vx
    @4
    @2
    @6
    @4
    wcel
    #
    wa
    #
    @7
    @11
    @7
    cc
    wcel
    @2
    @4
    cc
    @6
    @3
    @10
    ffvelrni
    adantl
    @12
    @6
    ccj
    @3
    ccom
    #
    cfv
    #
    @7
    ccj
    cfv
    #
    @7
    @12
    @9
    @11
    @14
    @15
    wceq
    @10
    @2
    @11
    simpr
    @4
    cc
    @6
    ccj
    @3
    fvco3
    sylancr
    @2
    @14
    @7
    wceq
    @11
    @2
    @6
    @13
    @3
    @2
    cr
    ccj
    cF
    ccom
    #
    cdv
    co
    #
    @13
    @3
    @0
    cA
    cc
    cF
    wf
    #
    @1
    @17
    @13
    wceq
    @0
    cr
    cc
    wss
    @18
    ax-resscn
    cA
    cr
    cc
    cF
    fss
    mpan2
    cF
    cA
    dvcj
    sylan
    @2
    @16
    cF
    cr
    cdv
    @2
    vy
    cA
    vy
    cv
    #
    cF
    cfv
    #
    ccj
    cfv
    #
    cmpt
    vy
    cA
    @20
    cmpt
    @16
    cF
    @2
    vy
    cA
    @21
    @20
    @2
    @19
    cA
    wcel
    #
    wa
    #
    @20
    @0
    @22
    @20
    cr
    wcel
    @1
    cA
    cr
    @19
    cF
    ffvelrn
    adantlr
    #
    cjred
    mpteq2dva
    @2
    vy
    vz
    cA
    cc
    @20
    vz
    cv
    #
    ccj
    cfv
    @21
    cF
    ccj
    @23
    @20
    @24
    recnd
    @2
    vy
    cA
    cr
    cF
    @0
    @1
    simpl
    feqmptd
    #
    @2
    vz
    cc
    cc
    ccj
    cc
    cc
    ccj
    wf
    @2
    cjf
    a1i
    feqmptd
    @25
    @20
    ccj
    fveq2
    fmptco
    @26
    3eqtr4d
    oveq2d
    eqtr3d
    fveq1d
    adantr
    eqtr3d
    cjrebd
    ralrimiva
    vx
    @4
    cr
    @3
    ffnfv
    sylanbrc
end
