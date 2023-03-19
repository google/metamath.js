include "c1stc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpw.mm"
include "ctop.mm"
include "is1stc2.mm"
include "simprbi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem 1stcclb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  assume 1stcclb.1: |- X = U. J

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint J f
  disjoint J g
  disjoint J k
  disjoint J n
  disjoint J w
  disjoint X g
  disjoint X k
  disjoint X n
  disjoint X w
  assert |- ( ( J e. 1stc /\ A e. X ) -> E. x e. ~P J ( x ~<_ _om /\ A. y e. J ( A e. y -> E. z e. x ( A e. z /\ z C_ y ) ) ) )

  proof
    cJ
    c1stc
    wcel
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vw
    cv
    #
    vy
    cv
    #
    wcel
    #
    @3
    vz
    cv
    #
    wcel
    #
    @6
    @4
    wss
    #
    wa
    #
    vz
    @1
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    #
    wa
    #
    vx
    cJ
    cpw
    #
    wrex
    #
    vw
    cX
    wral
    #
    cA
    cX
    wcel
    @2
    cA
    @4
    wcel
    #
    cA
    @6
    wcel
    #
    @8
    wa
    #
    vz
    @1
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    #
    wa
    #
    vx
    @14
    wrex
    #
    @0
    cJ
    ctop
    wcel
    @16
    vw
    vx
    vy
    vz
    cJ
    cX
    1stcclb.1
    is1stc2
    simprbi
    @15
    @24
    vw
    cA
    cX
    @3
    cA
    wceq
    #
    @13
    @23
    vx
    @14
    @25
    @12
    @22
    @2
    @25
    @11
    @21
    vy
    cJ
    @25
    @5
    @17
    @10
    @20
    @3
    cA
    @4
    eleq1
    @25
    @9
    @19
    vz
    @1
    @25
    @7
    @18
    @8
    @3
    cA
    @6
    eleq1
    anbi1d
    rexbidv
    imbi12d
    ralbidv
    anbi2d
    rexbidv
    rspcv
    mpan9
end
