include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ct0.mm"
include "wel.mm"
include "wb.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "cuni.mm"
include "ctop.mm"
include "topontop.mm"
include "eqid.mm"
include "ist0.mm"
include "baib.mm"
include "syl.mm"
include "toponuni.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "bitr4d.mm"

theorem ist0-2
  let vx: setvar x
  let vy: setvar y
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
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
  let cU: class U
  let cV: class V
  let cY: class Y

  disjoint x y
  disjoint o x
  disjoint o y
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A x
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
  disjoint o z
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Kol2 <-> A. x e. X A. y e. X ( A. o e. J ( x e. o <-> y e. o ) -> x = y ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ct0
    wcel
    #
    vx
    vo
    wel
    vy
    vo
    wel
    wb
    vo
    cJ
    wral
    vx
    vy
    weq
    wi
    #
    vy
    cJ
    cuni
    #
    wral
    #
    vx
    @3
    wral
    #
    @2
    vy
    cX
    wral
    #
    vx
    cX
    wral
    @0
    cJ
    ctop
    wcel
    #
    @1
    @5
    wb
    cX
    cJ
    topontop
    @1
    @7
    @5
    vx
    vy
    vo
    cJ
    @3
    @3
    eqid
    ist0
    baib
    syl
    @0
    @6
    @4
    vx
    cX
    @3
    cX
    cJ
    toponuni
    #
    @0
    @2
    vy
    cX
    @3
    @8
    raleqdv
    raleqbidv
    bitr4d
end
