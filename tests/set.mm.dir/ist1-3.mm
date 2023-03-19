include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ct1.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "cint.mm"
include "csn.mm"
include "ist1-2.mm"
include "wa.mm"
include "wb.mm"
include "wss.mm"
include "toponmax.mm"
include "eleq2.mm"
include "intminss.mm"
include "sylan.mm"
include "sselda.mm"
include "biimt.mm"
include "syl.mm"
include "ralbidva.mm"
include "id.mm"
include "rgenw.mm"
include "vex.mm"
include "elintrab.mm"
include "mpbir.mm"
include "snssi.mm"
include "ax-mp.mm"
include "eqss.mm"
include "mpbiran2.mm"
include "dfss3.mm"
include "bitri.mm"
include "velsn.mm"
include "equcom.mm"
include "imbi12i.mm"
include "ralbii.mm"
include "ralcom3.mm"
include "bitr3i.mm"
include "3bitr4g.mm"
include "bitr4d.mm"

theorem ist1-3
  let vx: setvar x
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
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

  disjoint o x
  disjoint J o
  disjoint J x
  disjoint X o
  disjoint X x
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
  disjoint o y
  disjoint o z
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Fre <-> A. x e. X |^| { o e. J | x e. o } = { x } ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ct1
    wcel
    vx
    vo
    wel
    #
    vy
    vo
    wel
    wi
    vo
    cJ
    wral
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
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
    @1
    vo
    cJ
    crab
    cint
    #
    @3
    csn
    #
    wceq
    #
    vx
    cX
    wral
    vx
    vy
    vo
    cJ
    cX
    ist1-2
    @0
    @10
    @7
    vx
    cX
    @0
    @3
    cX
    wcel
    #
    wa
    #
    @4
    @9
    wcel
    #
    vy
    @8
    wral
    #
    @4
    cX
    wcel
    #
    @13
    wi
    #
    vy
    @8
    wral
    #
    @10
    @7
    @12
    @13
    @16
    vy
    @8
    @12
    @4
    @8
    wcel
    #
    wa
    @15
    @13
    @16
    wb
    @12
    @8
    cX
    @4
    @0
    cX
    cJ
    wcel
    @11
    @8
    cX
    wss
    cX
    cJ
    toponmax
    @1
    @11
    vo
    cX
    cJ
    vo
    cv
    cX
    @3
    eleq2
    intminss
    sylan
    sselda
    @15
    @13
    biimt
    syl
    ralbidva
    @10
    @8
    @9
    wss
    #
    @14
    @10
    @19
    @9
    @8
    wss
    #
    @3
    @8
    wcel
    #
    @20
    @21
    @1
    @1
    wi
    #
    vo
    cJ
    wral
    @22
    vo
    cJ
    @1
    id
    rgenw
    @1
    vo
    @3
    cJ
    vx
    vex
    elintrab
    mpbir
    @3
    @8
    snssi
    ax-mp
    @8
    @9
    eqss
    mpbiran2
    vy
    @8
    @9
    dfss3
    bitri
    @7
    @18
    @13
    wi
    #
    vy
    cX
    wral
    @17
    @23
    @6
    vy
    cX
    @18
    @2
    @13
    @5
    @1
    vo
    @4
    cJ
    vy
    vex
    elintrab
    @13
    @4
    @3
    wceq
    @5
    vy
    @3
    velsn
    vy
    vx
    equcom
    bitri
    imbi12i
    ralbii
    @13
    vy
    cX
    @8
    ralcom3
    bitr3i
    3bitr4g
    ralbidva
    bitr4d
end
