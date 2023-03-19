include "cnrm.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "ccl.mm"
include "wa.mm"
include "wrex.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "wi.mm"
include "ctop.mm"
include "isnrm.mm"
include "wceq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "rspccv.mm"
include "simplbiim.mm"
include "elin.mm"
include "elpwg.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "cleq1lem.mm"
include "syl5bir.mm"
include "syl6.mm"
include "exp4a.mm"
include "3imp2.mm"

theorem nrmsep3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
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

  disjoint A x
  disjoint B x
  disjoint J x
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
  assert |- ( ( J e. Nrm /\ ( A e. J /\ B e. ( Clsd ` J ) /\ B C_ A ) ) -> E. x e. J ( B C_ x /\ ( ( cls ` J ) ` x ) C_ A ) )

  proof
    cJ
    cnrm
    wcel
    #
    cA
    cJ
    wcel
    #
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    cB
    cA
    wss
    #
    cB
    vx
    cv
    #
    wss
    @5
    cJ
    ccl
    cfv
    cfv
    #
    cA
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
    @3
    @4
    @9
    @0
    @1
    vz
    cv
    #
    @5
    wss
    #
    @7
    wa
    #
    vx
    cJ
    wrex
    #
    vz
    @2
    cA
    cpw
    #
    cin
    #
    wral
    #
    @3
    @4
    wa
    #
    @9
    wi
    @0
    cJ
    ctop
    wcel
    @11
    @6
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
    @2
    @18
    cpw
    #
    cin
    #
    wral
    #
    vy
    cJ
    wral
    @1
    @16
    wi
    vy
    vz
    vx
    cJ
    isnrm
    @24
    @16
    vy
    cA
    cJ
    @18
    cA
    wceq
    #
    @21
    @13
    vz
    @23
    @15
    @25
    @22
    @14
    @2
    @18
    cA
    pweq
    ineq2d
    @25
    @20
    @12
    vx
    cJ
    @25
    @19
    @7
    @11
    @18
    cA
    @6
    sseq2
    anbi2d
    rexbidv
    raleqbidv
    rspccv
    simplbiim
    @17
    cB
    @15
    wcel
    #
    @16
    @9
    @26
    @3
    cB
    @14
    wcel
    #
    wa
    @17
    cB
    @2
    @14
    elin
    @3
    @27
    @4
    cB
    cA
    @2
    elpwg
    pm5.32i
    bitri
    @13
    @9
    vz
    cB
    @15
    @10
    cB
    wceq
    @12
    @8
    vx
    cJ
    @7
    @10
    cB
    @5
    cleq1lem
    rexbidv
    rspccv
    syl5bir
    syl6
    exp4a
    3imp2
end
