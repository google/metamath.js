include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "crab.mm"
include "mrisval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "notbid.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "elpw2g.mm"
include "syl.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem ismri
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  assume ismri.1: |- N = ( mrCls ` A )
  assume ismri.2: |- I = ( mrInd ` A )

  disjoint A x
  disjoint S x
  disjoint A s
  disjoint s x
  disjoint S s
  disjoint X s
  disjoint N s
  assert |- ( A e. ( Moore ` X ) -> ( S e. I <-> ( S C_ X /\ A. x e. S -. x e. ( N ` ( S \ { x } ) ) ) ) )

  proof
    cA
    cX
    cmre
    cfv
    wcel
    #
    cS
    cI
    wcel
    #
    cS
    cX
    cpw
    #
    wcel
    #
    vx
    cv
    #
    cS
    @4
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cS
    wral
    #
    wa
    #
    cS
    cX
    wss
    #
    @10
    wa
    @0
    @1
    cS
    @4
    vs
    cv
    #
    @5
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @13
    wral
    #
    vs
    @2
    crab
    #
    wcel
    @11
    @0
    cI
    @19
    cS
    vx
    cA
    cI
    cN
    cX
    vs
    ismri.1
    ismri.2
    mrisval
    eleq2d
    @18
    @10
    vs
    cS
    @2
    @17
    @9
    vx
    @13
    cS
    @13
    cS
    wceq
    #
    @16
    @8
    @20
    @15
    @7
    @4
    @20
    @14
    @6
    cN
    @13
    cS
    @5
    difeq1
    fveq2d
    eleq2d
    notbid
    raleqbi1dv
    elrab
    syl6bb
    @0
    @3
    @12
    @10
    @0
    cX
    cvv
    wcel
    @3
    @12
    wb
    cA
    cX
    cmre
    elfvex
    cS
    cX
    cvv
    elpw2g
    syl
    anbi1d
    bitrd
end
