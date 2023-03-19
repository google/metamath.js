include "wcel.mm"
include "cv.mm"
include "crab.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "id.mm"
include "rabexg.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "fvmptg.mm"
include "syl2anr.mm"

theorem kqfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cU: class U
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint V x
  disjoint m n
  disjoint m o
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n o
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
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
  disjoint m u
  disjoint m v
  disjoint J m
  disjoint n u
  disjoint n v
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint J o
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F o
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint U w
  disjoint U z
  assert |- ( ( J e. V /\ A e. X ) -> ( F ` A ) = { y e. J | A e. y } )

  proof
    cA
    cX
    wcel
    #
    @0
    cA
    vy
    cv
    #
    wcel
    #
    vy
    cJ
    crab
    #
    cvv
    wcel
    cA
    cF
    cfv
    @3
    wceq
    cJ
    cV
    wcel
    @0
    id
    @2
    vy
    cJ
    cV
    rabexg
    vx
    cA
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cJ
    crab
    @3
    cX
    cvv
    cF
    @4
    cA
    wceq
    @5
    @2
    vy
    cJ
    @4
    cA
    @1
    eleq1
    rabbidv
    kqval.2
    fvmptg
    syl2anr
end
