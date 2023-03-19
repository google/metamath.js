include "wne.mm"
include "cpr.mm"
include "wf.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cfv.mm"
include "wcel.mm"
include "prid1.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "adantr.mm"
include "prid2.mm"
include "wral.mm"
include "fvex.mm"
include "fvpr1.mm"
include "fvpr2.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ralpr.mm"
include "sylanbrc.mm"
include "adantl.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fpr.mm"
include "syl.mm"
include "eqfnfv.mm"
include "syl2an.mm"
include "mpbird.mm"
include "opeq2.mm"
include "preq1d.mm"
include "eqeq2d.mm"
include "preq2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "expcom.mm"
include "wi.mm"
include "wss.mm"
include "vex.mm"
include "prssi.mm"
include "fss.mm"
include "ex.mm"
include "feq1.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdvv.mm"
include "impbid.mm"

theorem fprb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  assume fprb.1: |- A e. _V
  assume fprb.2: |- B e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  assert |- ( A =/= B -> ( F : { A , B } --> R <-> E. x e. R E. y e. R F = { <. A , x >. , <. B , y >. } ) )

  proof
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    #
    cR
    cF
    wf
    #
    cF
    cA
    vx
    cv
    #
    cop
    #
    cB
    vy
    cv
    #
    cop
    #
    cpr
    #
    wceq
    #
    vy
    cR
    wrex
    vx
    cR
    wrex
    #
    @2
    @0
    @9
    @2
    @0
    wa
    #
    cA
    cF
    cfv
    #
    cR
    wcel
    #
    cB
    cF
    cfv
    #
    cR
    wcel
    #
    cF
    cA
    @11
    cop
    #
    cB
    @13
    cop
    #
    cpr
    #
    wceq
    #
    @9
    @2
    @12
    @0
    @2
    cA
    @1
    wcel
    @12
    cA
    cB
    fprb.1
    prid1
    @1
    cR
    cA
    cF
    ffvelrn
    mpan2
    adantr
    @2
    @14
    @0
    @2
    cB
    @1
    wcel
    @14
    cA
    cB
    fprb.2
    prid2
    @1
    cR
    cB
    cF
    ffvelrn
    mpan2
    adantr
    @10
    @18
    @3
    cF
    cfv
    #
    @3
    @17
    cfv
    #
    wceq
    #
    vx
    @1
    wral
    #
    @0
    @22
    @2
    @0
    cA
    @17
    cfv
    #
    @11
    wceq
    #
    cB
    @17
    cfv
    #
    @13
    wceq
    #
    @22
    cA
    cB
    @11
    @13
    fprb.1
    cA
    cF
    fvex
    #
    fvpr1
    cA
    cB
    @11
    @13
    fprb.2
    cB
    cF
    fvex
    #
    fvpr2
    @21
    @24
    @26
    vx
    cA
    cB
    fprb.1
    fprb.2
    @3
    cA
    wceq
    #
    @21
    @11
    @23
    wceq
    @24
    @29
    @19
    @11
    @20
    @23
    @3
    cA
    cF
    fveq2
    @3
    cA
    @17
    fveq2
    eqeq12d
    @11
    @23
    eqcom
    syl6bb
    @3
    cB
    wceq
    #
    @21
    @13
    @25
    wceq
    @26
    @30
    @19
    @13
    @20
    @25
    @3
    cB
    cF
    fveq2
    @3
    cB
    @17
    fveq2
    eqeq12d
    @13
    @25
    eqcom
    syl6bb
    ralpr
    sylanbrc
    adantl
    @2
    cF
    @1
    wfn
    @17
    @1
    wfn
    #
    @18
    @22
    wb
    @0
    @1
    cR
    cF
    ffn
    @0
    @1
    @11
    @13
    cpr
    #
    @17
    wf
    @31
    cA
    cB
    @11
    @13
    fprb.1
    fprb.2
    @27
    @28
    fpr
    @1
    @32
    @17
    ffn
    syl
    vx
    @1
    cF
    @17
    eqfnfv
    syl2an
    mpbird
    @8
    @18
    cF
    @15
    @6
    cpr
    #
    wceq
    vx
    vy
    @11
    @13
    cR
    cR
    @3
    @11
    wceq
    #
    @7
    @33
    cF
    @34
    @4
    @15
    @6
    @3
    @11
    cA
    opeq2
    preq1d
    eqeq2d
    @5
    @13
    wceq
    #
    @33
    @17
    cF
    @35
    @6
    @16
    @15
    @5
    @13
    cB
    opeq2
    preq2d
    eqeq2d
    rspc2ev
    syl3anc
    expcom
    @0
    @8
    @2
    vx
    vy
    cR
    cR
    @0
    @3
    cR
    wcel
    @5
    cR
    wcel
    wa
    #
    @1
    cR
    @7
    wf
    #
    @8
    @2
    wi
    @0
    @36
    @37
    @0
    @1
    @3
    @5
    cpr
    #
    @7
    wf
    @38
    cR
    wss
    @37
    @36
    cA
    cB
    @3
    @5
    fprb.1
    fprb.2
    vx
    vex
    vy
    vex
    fpr
    @3
    @5
    cR
    prssi
    @1
    @38
    cR
    @7
    fss
    syl2an
    ex
    @8
    @2
    @37
    @1
    cR
    cF
    @7
    feq1
    biimprcd
    syl6
    rexlimdvv
    impbid
end
