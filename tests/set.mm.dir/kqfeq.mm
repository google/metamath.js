include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "crab.mm"
include "wb.mm"
include "wral.mm"
include "kqfval.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "rabbi.mm"
include "syl6bbr.mm"

theorem kqfeq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
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
  disjoint B x
  disjoint B y
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
  assert |- ( ( J e. V /\ A e. X /\ B e. X ) -> ( ( F ` A ) = ( F ` B ) <-> A. y e. J ( A e. y <-> B e. y ) ) )

  proof
    cJ
    cV
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wceq
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
    cB
    @6
    wcel
    #
    vy
    cJ
    crab
    #
    wceq
    @7
    @9
    wb
    vy
    cJ
    wral
    @3
    @4
    @8
    @5
    @10
    @0
    @1
    @4
    @8
    wceq
    @2
    vx
    vy
    cA
    cF
    cJ
    cV
    cX
    kqval.2
    kqfval
    3adant3
    @0
    @2
    @5
    @10
    wceq
    @1
    vx
    vy
    cB
    cF
    cJ
    cV
    cX
    kqval.2
    kqfval
    3adant2
    eqeq12d
    @7
    @9
    vy
    cJ
    rabbi
    syl6bbr
end
