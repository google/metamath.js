include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "wrex.mm"
include "wf.mm"
include "wb.mm"
include "elpw2g.mm"
include "biimprd.mm"
include "ralimdv.mm"
include "imp.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "elrfirn.mm"
include "syldan.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "fveq2.mm"
include "cbviin.mm"
include "cvv.mm"
include "simplr.mm"
include "simpll.mm"
include "simpr.mm"
include "ssexd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralimdva.mm"
include "ssralv.mm"
include "mpan9.mm"
include "iineq2.mm"
include "syl.mm"
include "syl5eq.mm"
include "ineq2d.mm"
include "eqeq2d.mm"
include "sylan2.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem elrfirn2
  let vy: setvar y
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cI: class I
  let cV: class V
  let vz: setvar z

  disjoint A v
  disjoint B v
  disjoint B y
  disjoint v y
  disjoint C v
  disjoint I v
  disjoint I y
  disjoint V v
  disjoint V y
  disjoint C z
  disjoint v z
  disjoint I z
  disjoint y z
  assert |- ( ( B e. V /\ A. y e. I C C_ B ) -> ( A e. ( fi ` ( { B } u. ran ( y e. I |-> C ) ) ) <-> E. v e. ( ~P I i^i Fin ) A = ( B i^i |^|_ y e. v C ) ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cB
    wss
    #
    vy
    cI
    wral
    #
    wa
    #
    cA
    cB
    csn
    vy
    cI
    cC
    cmpt
    #
    crn
    cun
    cfi
    cfv
    wcel
    #
    cA
    cB
    vz
    vv
    cv
    #
    vz
    cv
    #
    @4
    cfv
    #
    ciin
    #
    cin
    #
    wceq
    #
    vv
    cI
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cA
    cB
    vy
    @6
    cC
    ciin
    #
    cin
    #
    wceq
    #
    vv
    @13
    wrex
    @0
    @2
    cI
    cB
    cpw
    #
    @4
    wf
    #
    @5
    @14
    wb
    @3
    cC
    @18
    wcel
    #
    vy
    cI
    wral
    #
    @19
    @0
    @2
    @21
    @0
    @1
    @20
    vy
    cI
    @0
    @20
    @1
    cC
    cB
    cV
    elpw2g
    biimprd
    ralimdv
    imp
    vy
    cI
    @18
    cC
    @4
    @4
    eqid
    #
    fmpt
    sylib
    vz
    vv
    cA
    cB
    @4
    cI
    cV
    elrfirn
    syldan
    @3
    @11
    @17
    vv
    @13
    @6
    @13
    wcel
    #
    @3
    @6
    cI
    wss
    #
    @11
    @17
    wb
    @23
    @6
    cI
    @13
    @12
    @6
    @12
    cfn
    inss1
    sseli
    elpwid
    @3
    @24
    wa
    #
    @10
    @16
    cA
    @25
    @9
    @15
    cB
    @25
    @9
    vy
    @6
    vy
    cv
    #
    @4
    cfv
    #
    ciin
    #
    @15
    vz
    vy
    @6
    @8
    @27
    vy
    cI
    cC
    @7
    nffvmpt1
    vz
    @27
    nfcv
    @7
    @26
    @4
    fveq2
    cbviin
    @25
    @27
    cC
    wceq
    #
    vy
    @6
    wral
    #
    @28
    @15
    wceq
    @3
    @29
    vy
    cI
    wral
    #
    @24
    @30
    @0
    @2
    @31
    @0
    @1
    @29
    vy
    cI
    @0
    @26
    cI
    wcel
    #
    wa
    #
    @1
    @29
    @33
    @1
    wa
    #
    @32
    cC
    cvv
    wcel
    @29
    @0
    @32
    @1
    simplr
    @34
    cC
    cB
    cV
    @0
    @32
    @1
    simpll
    @33
    @1
    simpr
    ssexd
    vy
    cI
    cC
    cvv
    @4
    @22
    fvmpt2
    syl2anc
    ex
    ralimdva
    imp
    @29
    vy
    @6
    cI
    ssralv
    mpan9
    vy
    @6
    @27
    cC
    iineq2
    syl
    syl5eq
    ineq2d
    eqeq2d
    sylan2
    rexbidva
    bitrd
end
