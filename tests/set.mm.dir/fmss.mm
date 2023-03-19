include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "w3a.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "co.mm"
include "cfm.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl1.mm"
include "eqid.mm"
include "fbasrn.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "cres.mm"
include "wceq.mm"
include "resmpt.mm"
include "ad2antll.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "rnss.mm"
include "syl.mm"
include "fgss.mm"
include "fmval.mm"
include "3sstr4d.mm"

theorem fmss
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cX: class X
  let cY: class Y
  let vy: setvar y


  assert |- ( ( ( X e. A /\ B e. ( fBas ` Y ) /\ C e. ( fBas ` Y ) ) /\ ( F : Y --> X /\ B C_ C ) ) -> ( ( X FilMap F ) ` B ) C_ ( ( X FilMap F ) ` C ) )

  proof
    cX
    cA
    wcel
    #
    cB
    cY
    cfbas
    cfv
    #
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cY
    cX
    cF
    wf
    #
    cB
    cC
    wss
    #
    wa
    #
    wa
    #
    cX
    vy
    cB
    cF
    vy
    cv
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cX
    vy
    cC
    @9
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cB
    cX
    cF
    cfm
    co
    #
    cfv
    #
    cC
    @16
    cfv
    #
    @8
    @11
    cX
    cfbas
    cfv
    #
    wcel
    #
    @14
    @19
    wcel
    #
    @11
    @14
    wss
    #
    @12
    @15
    wss
    @8
    @2
    @5
    @0
    @20
    @0
    @2
    @3
    @7
    simpl2
    #
    @4
    @5
    @6
    simprl
    #
    @0
    @2
    @3
    @7
    simpl1
    #
    vy
    cB
    @11
    cF
    cA
    cY
    cX
    @11
    eqid
    fbasrn
    syl3anc
    @8
    @3
    @5
    @0
    @21
    @0
    @2
    @3
    @7
    simpl3
    #
    @24
    @25
    vy
    cC
    @14
    cF
    cA
    cY
    cX
    @14
    eqid
    fbasrn
    syl3anc
    @8
    @10
    @13
    wss
    @22
    @8
    @10
    @13
    cB
    cres
    #
    @13
    @6
    @27
    @10
    wceq
    @4
    @5
    vy
    cC
    cB
    @9
    resmpt
    ad2antll
    @13
    cB
    resss
    syl6eqssr
    @10
    @13
    rnss
    syl
    @11
    @14
    cX
    fgss
    syl3anc
    @8
    @0
    @2
    @5
    @17
    @12
    wceq
    @25
    @23
    @24
    vy
    cA
    cB
    cF
    cX
    cY
    fmval
    syl3anc
    @8
    @0
    @3
    @5
    @18
    @15
    wceq
    @25
    @26
    @24
    vy
    cA
    cC
    cF
    cX
    cY
    fmval
    syl3anc
    3sstr4d
end
