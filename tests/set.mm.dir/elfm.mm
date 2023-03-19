include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "fmval.mm"
include "eleq2d.mm"
include "wb.mm"
include "eqid.mm"
include "fbasrn.mm"
include "3comr.mm"
include "elfg.mm"
include "syl.mm"
include "wceq.mm"
include "simpr.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "cvv.mm"
include "simpl1.mm"
include "imassrn.mm"
include "frn.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "syl5ss.mm"
include "ssexd.mm"
include "elrnmpt.mm"
include "mpbird.mm"
include "cbvmptv.mm"
include "ibi.mm"
include "adantl.mm"
include "sseq1d.mm"
include "rexxfrd.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem elfm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let cL: class L

  disjoint B x
  disjoint C x
  disjoint F x
  disjoint X x
  disjoint A x
  disjoint Y x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C s
  disjoint C t
  disjoint C y
  disjoint F s
  disjoint F t
  disjoint F y
  disjoint X s
  disjoint X t
  disjoint X y
  disjoint A y
  disjoint L s
  disjoint L x
  disjoint L y
  disjoint Y s
  disjoint Y t
  disjoint Y y
  assert |- ( ( X e. C /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( A e. ( ( X FilMap F ) ` B ) <-> ( A C_ X /\ E. x e. B ( F " x ) C_ A ) ) )

  proof
    cX
    cC
    wcel
    #
    cB
    cY
    cfbas
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cB
    cX
    cF
    cfm
    co
    cfv
    #
    wcel
    cA
    cX
    vt
    cB
    cF
    vt
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
    wcel
    #
    cA
    cX
    wss
    #
    vy
    cv
    #
    cA
    wss
    #
    vy
    @8
    wrex
    #
    wa
    #
    @11
    cF
    vx
    cv
    #
    cima
    #
    cA
    wss
    #
    vx
    cB
    wrex
    #
    wa
    @3
    @4
    @9
    cA
    vt
    cC
    cB
    cF
    cX
    cY
    fmval
    eleq2d
    @3
    @8
    cX
    cfbas
    cfv
    wcel
    #
    @10
    @15
    wb
    @1
    @2
    @0
    @20
    vt
    cB
    @8
    cF
    cC
    cY
    cX
    @8
    eqid
    fbasrn
    3comr
    vy
    cA
    @8
    cX
    elfg
    syl
    @3
    @14
    @19
    @11
    @3
    @13
    @18
    vy
    vx
    @17
    @8
    cB
    @3
    @16
    cB
    wcel
    #
    wa
    #
    @17
    @8
    wcel
    #
    @17
    @6
    wceq
    #
    vt
    cB
    wrex
    #
    @22
    @21
    @17
    @17
    wceq
    #
    @25
    @3
    @21
    simpr
    @17
    eqid
    @24
    @26
    vt
    @16
    cB
    @5
    @16
    wceq
    @6
    @17
    @17
    @5
    @16
    cF
    imaeq2
    #
    eqeq2d
    rspcev
    sylancl
    @22
    @17
    cvv
    wcel
    @23
    @25
    wb
    @22
    @17
    cX
    cC
    @0
    @1
    @2
    @21
    simpl1
    @22
    @17
    cF
    crn
    #
    cX
    cF
    @16
    imassrn
    @3
    @28
    cX
    wss
    #
    @21
    @2
    @0
    @29
    @1
    cY
    cX
    cF
    frn
    3ad2ant3
    adantr
    syl5ss
    ssexd
    vt
    cB
    @6
    @17
    @7
    cvv
    @7
    eqid
    elrnmpt
    syl
    mpbird
    @12
    @8
    wcel
    #
    @12
    @17
    wceq
    #
    vx
    cB
    wrex
    #
    @3
    @30
    @32
    vx
    cB
    @17
    @12
    @7
    @8
    vt
    vx
    cB
    @6
    @17
    @27
    cbvmptv
    elrnmpt
    ibi
    adantl
    @3
    @31
    wa
    @12
    @17
    cA
    @3
    @31
    simpr
    sseq1d
    rexxfrd
    anbi2d
    3bitrd
end
