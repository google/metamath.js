include "cv.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "wa.mm"
include "wrex.mm"
include "ccld.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "ctop.mm"
include "cnrm.mm"
include "wceq.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "fveq1d.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "rexeqbi1dv.mm"
include "raleqbidv.mm"
include "raleqbi1dv.mm"
include "df-nrm.mm"
include "elrab2.mm"

theorem isnrm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let cA: class A
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
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint A x
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
  disjoint U x
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
  assert |- ( J e. Nrm <-> ( J e. Top /\ A. x e. J A. y e. ( ( Clsd ` J ) i^i ~P x ) E. z e. J ( y C_ z /\ ( ( cls ` J ) ` z ) C_ x ) ) )

  proof
    vy
    cv
    vz
    cv
    #
    wss
    #
    @0
    vj
    cv
    #
    ccl
    cfv
    #
    cfv
    #
    vx
    cv
    #
    wss
    #
    wa
    #
    vz
    @2
    wrex
    #
    vy
    @2
    ccld
    cfv
    #
    @5
    cpw
    #
    cin
    #
    wral
    #
    vx
    @2
    wral
    @1
    @0
    cJ
    ccl
    cfv
    #
    cfv
    #
    @5
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    vy
    cJ
    ccld
    cfv
    #
    @10
    cin
    #
    wral
    #
    vx
    cJ
    wral
    vj
    cJ
    ctop
    cnrm
    @12
    @20
    vx
    @2
    cJ
    @2
    cJ
    wceq
    #
    @8
    @17
    vy
    @11
    @19
    @21
    @9
    @18
    @10
    @2
    cJ
    ccld
    fveq2
    ineq1d
    @7
    @16
    vz
    @2
    cJ
    @21
    @6
    @15
    @1
    @21
    @4
    @14
    @5
    @21
    @0
    @3
    @13
    @2
    cJ
    ccl
    fveq2
    fveq1d
    sseq1d
    anbi2d
    rexeqbi1dv
    raleqbidv
    raleqbi1dv
    vx
    vy
    vz
    vj
    df-nrm
    elrab2
end
