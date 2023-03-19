include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cismty.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "wceq.mm"
include "wral.mm"
include "cab.mm"
include "ismtyval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wi.mm"
include "wb.mm"
include "wf.mm"
include "cdm.mm"
include "f1of.mm"
include "adantr.mm"
include "elfvdm.mm"
include "fex2.mm"
include "syl3an.mm"
include "3expib.mm"
include "com12.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "elab3g.mm"
include "syl.mm"
include "bitrd.mm"

theorem isismty
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vf: setvar f

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint F x
  disjoint F y
  disjoint M f
  disjoint f x
  disjoint f y
  disjoint N f
  disjoint X f
  disjoint Y f
  disjoint F f
  assert |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) -> ( F e. ( M Ismty N ) <-> ( F : X -1-1-onto-> Y /\ A. x e. X A. y e. X ( x M y ) = ( ( F ` x ) N ( F ` y ) ) ) ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    wa
    #
    cF
    cM
    cN
    cismty
    co
    #
    wcel
    cF
    cX
    cY
    vf
    cv
    #
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    @6
    @4
    cfv
    #
    @7
    @4
    cfv
    #
    cN
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    vf
    cab
    #
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    @8
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cN
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    @2
    @3
    @15
    cF
    vx
    vy
    vf
    cM
    cN
    cX
    cY
    ismtyval
    eleq2d
    @2
    @23
    cF
    cvv
    wcel
    #
    wi
    @16
    @23
    wb
    @23
    @2
    @24
    @23
    @0
    @1
    @24
    @23
    cX
    cY
    cF
    wf
    #
    @0
    cX
    cxmt
    cdm
    #
    wcel
    @1
    cY
    @26
    wcel
    @24
    @17
    @25
    @22
    cX
    cY
    cF
    f1of
    adantr
    cM
    cX
    cxmt
    elfvdm
    cN
    cY
    cxmt
    elfvdm
    cX
    cY
    cF
    @26
    @26
    fex2
    syl3an
    3expib
    com12
    @14
    @23
    vf
    cF
    cvv
    @4
    cF
    wceq
    #
    @5
    @17
    @13
    @22
    cX
    cY
    @4
    cF
    f1oeq1
    @27
    @12
    @21
    vx
    vy
    cX
    cX
    @27
    @11
    @20
    @8
    @27
    @9
    @18
    @10
    @19
    cN
    @6
    @4
    cF
    fveq1
    @7
    @4
    cF
    fveq1
    oveq12d
    eqeq2d
    2ralbidv
    anbi12d
    elab3g
    syl
    bitrd
end
