include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "recnd.mm"
include "rered.mm"
include "breqtrrd.mm"
include "rlimrege0.mm"
include "rlimrecl.mm"
include "breqtrd.mm"

theorem rlimge0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cR: class R
  assume rlimcld2.1: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimcld2.2: |- ( ph -> ( x e. A |-> B ) ~~>r C )
  assume rlimrecl.3: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume rlimge0.4: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint r w
  disjoint B r
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C r
  disjoint w x
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint D r
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint R z
  assert |- ( ph -> 0 <_ C )

  proof
    wph
    cc0
    cC
    cre
    cfv
    cC
    cle
    wph
    vx
    cA
    cB
    cC
    rlimcld2.1
    rlimcld2.2
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    rlimrecl.3
    recnd
    @0
    cc0
    cB
    cB
    cre
    cfv
    cle
    rlimge0.4
    @0
    cB
    rlimrecl.3
    rered
    breqtrrd
    rlimrege0
    wph
    cC
    wph
    vx
    cA
    cB
    cC
    rlimcld2.1
    rlimcld2.2
    rlimrecl.3
    rlimrecl
    rered
    breqtrd
end
