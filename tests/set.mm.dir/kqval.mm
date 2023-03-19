include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "cuni.mm"
include "cv.mm"
include "crab.mm"
include "cmpt.mm"
include "cqtop.mm"
include "co.mm"
include "ctop.mm"
include "wceq.mm"
include "topontop.mm"
include "id.mm"
include "unieq.mm"
include "rabeq.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "df-kq.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "toponuni.mm"
include "mpteq1d.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem kqval
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cU: class U
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
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
  disjoint A x
  disjoint y z
  disjoint A y
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
  disjoint V x
  assert |- ( J e. ( TopOn ` X ) -> ( KQ ` J ) = ( J qTop F ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ckq
    cfv
    #
    cJ
    vx
    cJ
    cuni
    #
    vx
    cv
    vy
    cv
    wcel
    #
    vy
    cJ
    crab
    #
    cmpt
    #
    cqtop
    co
    #
    cJ
    cF
    cqtop
    co
    @0
    cJ
    ctop
    wcel
    @1
    @6
    wceq
    cX
    cJ
    topontop
    vj
    cJ
    vj
    cv
    #
    vx
    @7
    cuni
    #
    @3
    vy
    @7
    crab
    #
    cmpt
    #
    cqtop
    co
    @6
    ctop
    ckq
    @7
    cJ
    wceq
    #
    @7
    cJ
    @10
    @5
    cqtop
    @11
    id
    @11
    vx
    @8
    @9
    @2
    @4
    @7
    cJ
    unieq
    @3
    vy
    @7
    cJ
    rabeq
    mpteq12dv
    oveq12d
    vx
    vy
    vj
    df-kq
    cJ
    @5
    cqtop
    ovex
    fvmpt
    syl
    @0
    cF
    @5
    cJ
    cqtop
    @0
    cF
    vx
    cX
    @4
    cmpt
    @5
    kqval.2
    @0
    vx
    cX
    @2
    @4
    cX
    cJ
    toponuni
    mpteq1d
    syl5eq
    oveq2d
    eqtr4d
end
