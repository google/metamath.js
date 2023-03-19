include "creg.mm"
include "wcel.mm"
include "cv.mm"
include "ccl.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "ctop.mm"
include "isreg.mm"
include "wceq.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "rspccv.mm"
include "simplbiim.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "syl6.mm"
include "3imp.mm"

theorem regsep
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint A x
  disjoint J x
  disjoint U x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c o
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint J c
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint J d
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f o
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint J f
  disjoint g j
  disjoint g m
  disjoint g n
  disjoint g o
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint J g
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m o
  disjoint J m
  disjoint n o
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint J o
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( ( J e. Reg /\ U e. J /\ A e. U ) -> E. x e. J ( A e. x /\ ( ( cls ` J ) ` x ) C_ U ) )

  proof
    cJ
    creg
    wcel
    #
    cU
    cJ
    wcel
    #
    cA
    cU
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    @3
    cJ
    ccl
    cfv
    cfv
    #
    cU
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @0
    @1
    vz
    cv
    #
    @3
    wcel
    #
    @6
    wa
    #
    vx
    cJ
    wrex
    #
    vz
    cU
    wral
    #
    @2
    @8
    wi
    @0
    cJ
    ctop
    wcel
    @10
    @5
    vy
    cv
    #
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    vz
    @14
    wral
    #
    vy
    cJ
    wral
    @1
    @13
    wi
    vy
    vz
    vx
    cJ
    isreg
    @18
    @13
    vy
    cU
    cJ
    @17
    @12
    vz
    @14
    cU
    @14
    cU
    wceq
    #
    @16
    @11
    vx
    cJ
    @19
    @15
    @6
    @10
    @14
    cU
    @5
    sseq2
    anbi2d
    rexbidv
    raleqbi1dv
    rspccv
    simplbiim
    @12
    @8
    vz
    cA
    cU
    @9
    cA
    wceq
    #
    @11
    @7
    vx
    cJ
    @20
    @10
    @4
    @6
    @9
    cA
    @3
    eleq1
    anbi1d
    rexbidv
    rspccv
    syl6
    3imp
end
