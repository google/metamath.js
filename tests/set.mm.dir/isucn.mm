include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cucn.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wf.mm"
include "crab.mm"
include "ucnval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq1.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem isucn
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vr: setvar r
  let vf: setvar f

  disjoint r s
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint U r
  disjoint U s
  disjoint U x
  disjoint U y
  disjoint V r
  disjoint V s
  disjoint V x
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y r
  disjoint Y s
  disjoint Y x
  disjoint f r
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint U f
  disjoint V f
  disjoint X f
  disjoint Y f
  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. ( UnifOn ` Y ) ) -> ( F e. ( U uCn V ) <-> ( F : X --> Y /\ A. s e. V E. r e. U A. x e. X A. y e. X ( x r y -> ( F ` x ) s ( F ` y ) ) ) ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cY
    cust
    cfv
    wcel
    #
    wa
    #
    cF
    cU
    cV
    cucn
    co
    #
    wcel
    #
    cF
    cY
    cX
    cmap
    co
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    wbr
    #
    @7
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    vs
    cv
    #
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    vr
    cU
    wrex
    #
    vs
    cV
    wral
    #
    wa
    #
    cX
    cY
    cF
    wf
    #
    @17
    wa
    @2
    @4
    cF
    @9
    @7
    vf
    cv
    #
    cfv
    #
    @8
    @20
    cfv
    #
    @12
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    vr
    cU
    wrex
    #
    vs
    cV
    wral
    #
    vf
    @5
    crab
    #
    wcel
    @18
    @2
    @3
    @28
    cF
    vx
    vy
    cU
    vf
    cV
    cX
    cY
    vs
    vr
    ucnval
    eleq2d
    @27
    @17
    vf
    cF
    @5
    @20
    cF
    wceq
    #
    @26
    @16
    vs
    cV
    @29
    @25
    @15
    vr
    vx
    cU
    cX
    @29
    @24
    @14
    vy
    cX
    @29
    @23
    @13
    @9
    @29
    @21
    @10
    @22
    @11
    @12
    @7
    @20
    cF
    fveq1
    @8
    @20
    cF
    fveq1
    breq12d
    imbi2d
    ralbidv
    rexralbidv
    ralbidv
    elrab
    syl6bb
    @2
    @6
    @19
    @17
    @1
    cY
    cvv
    wcel
    cX
    cvv
    wcel
    @6
    @19
    wb
    @0
    cV
    cY
    cust
    elfvex
    cU
    cX
    cust
    elfvex
    cY
    cX
    cF
    cvv
    cvv
    elmapg
    syl2anr
    anbi1d
    bitrd
end
