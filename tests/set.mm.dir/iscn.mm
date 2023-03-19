include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "cnfval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "wb.mm"
include "toponmax.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem iscn
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cP: class P

  disjoint J y
  disjoint K y
  disjoint X y
  disjoint F y
  disjoint Y y
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint g j
  disjoint g k
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j k
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint x y
  disjoint J x
  disjoint K f
  disjoint K j
  disjoint K k
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint X f
  disjoint X j
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint F f
  disjoint F x
  disjoint P f
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. y e. K ( `' F " y ) e. J ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    cF
    vf
    cv
    #
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vy
    cK
    wral
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    #
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    @6
    cima
    #
    cJ
    wcel
    #
    vy
    cK
    wral
    #
    wa
    #
    @2
    @3
    @11
    cF
    vy
    vf
    cJ
    cK
    cX
    cY
    cnfval
    eleq2d
    @12
    cF
    @10
    wcel
    #
    @17
    wa
    @2
    @18
    @9
    @17
    vf
    cF
    @10
    @4
    cF
    wceq
    #
    @8
    @16
    vy
    cK
    @20
    @7
    @15
    cJ
    @20
    @5
    @14
    @6
    @4
    cF
    cnveq
    imaeq1d
    eleq1d
    ralbidv
    elrab
    @2
    @19
    @13
    @17
    @1
    cY
    cK
    wcel
    cX
    cJ
    wcel
    @19
    @13
    wb
    @0
    cY
    cK
    toponmax
    cX
    cJ
    toponmax
    cY
    cX
    cF
    cK
    cJ
    elmapg
    syl2anr
    anbi1d
    syl5bb
    bitrd
end
