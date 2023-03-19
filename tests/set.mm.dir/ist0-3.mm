include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ct0.mm"
include "wel.mm"
include "wb.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "cv.mm"
include "wne.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wrex.mm"
include "ist0-2.mm"
include "con34b.mm"
include "df-ne.mm"
include "xor.mm"
include "ancom.mm"
include "orbi2i.mm"
include "bitri.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitr3i.mm"
include "imbi12i.mm"
include "bitr4i.mm"
include "2ralbii.mm"
include "syl6bb.mm"

theorem ist0-3
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
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Kol2 <-> A. x e. X A. y e. X ( x =/= y -> E. o e. J ( ( x e. o /\ -. y e. o ) \/ ( -. x e. o /\ y e. o ) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    cJ
    ct0
    wcel
    vx
    vo
    wel
    #
    vy
    vo
    wel
    #
    wb
    #
    vo
    cJ
    wral
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @0
    @1
    wn
    wa
    #
    @0
    wn
    #
    @1
    wa
    #
    wo
    #
    vo
    cJ
    wrex
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    vx
    vy
    vo
    cJ
    cX
    ist0-2
    @5
    @14
    vx
    vy
    cX
    cX
    @5
    @4
    wn
    #
    @3
    wn
    #
    wi
    @14
    @3
    @4
    con34b
    @8
    @15
    @13
    @16
    @6
    @7
    df-ne
    @13
    @2
    wn
    #
    vo
    cJ
    wrex
    @16
    @17
    @12
    vo
    cJ
    @17
    @9
    @1
    @10
    wa
    #
    wo
    @12
    @0
    @1
    xor
    @18
    @11
    @9
    @1
    @10
    ancom
    orbi2i
    bitri
    rexbii
    @2
    vo
    cJ
    rexnal
    bitr3i
    imbi12i
    bitr4i
    2ralbii
    syl6bb
end
