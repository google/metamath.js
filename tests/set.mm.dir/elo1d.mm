include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clo1.mm"
include "cv.mm"
include "wa.mm"
include "abscld.mm"
include "ello1d.mm"
include "lo1o12.mm"
include "mpbird.mm"

theorem elo1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  assume elo1mpt.1: |- ( ph -> A C_ RR )
  assume elo1mpt.2: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume elo1d.3: |- ( ph -> C e. RR )
  assume elo1d.4: |- ( ph -> M e. RR )
  assume elo1d.5: |- ( ( ph /\ ( x e. A /\ C <_ x ) ) -> ( abs ` B ) <_ M )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint M x
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint C m
  disjoint C y
  disjoint m ph
  disjoint ph y
  disjoint M m
  assert |- ( ph -> ( x e. A |-> B ) e. O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    co1
    wcel
    vx
    cA
    cB
    cabs
    cfv
    #
    cmpt
    clo1
    wcel
    wph
    vx
    cA
    @0
    cC
    cM
    elo1mpt.1
    wph
    vx
    cv
    cA
    wcel
    wa
    cB
    elo1mpt.2
    abscld
    elo1d.3
    elo1d.4
    elo1d.5
    ello1d
    wph
    vx
    cA
    cB
    elo1mpt.2
    lo1o12
    mpbird
end
