include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "abscld.mm"
include "cmpt.mm"
include "co1.mm"
include "clo1.mm"
include "lo1o12.mm"
include "mpbid.mm"
include "lo1bdd2.mm"

theorem o1bdd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let cM: class M
  assume o1bdd2.1: |- ( ph -> A C_ RR )
  assume o1bdd2.2: |- ( ph -> C e. RR )
  assume o1bdd2.3: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume o1bdd2.4: |- ( ph -> ( x e. A |-> B ) e. O(1) )
  assume o1bdd2.5: |- ( ( ph /\ ( y e. RR /\ C <_ y ) ) -> M e. RR )
  assume o1bdd2.6: |- ( ( ( ph /\ x e. A ) /\ ( ( y e. RR /\ C <_ y ) /\ x < y ) ) -> ( abs ` B ) <_ M )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint M m
  disjoint M x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. m e. RR A. x e. A ( abs ` B ) <_ m )

  proof
    wph
    vx
    vy
    cA
    cB
    cabs
    cfv
    #
    cC
    vm
    cM
    o1bdd2.1
    o1bdd2.2
    wph
    vx
    cv
    cA
    wcel
    wa
    cB
    o1bdd2.3
    abscld
    wph
    vx
    cA
    cB
    cmpt
    co1
    wcel
    vx
    cA
    @0
    cmpt
    clo1
    wcel
    o1bdd2.4
    wph
    vx
    cA
    cB
    o1bdd2.3
    lo1o12
    mpbid
    o1bdd2.5
    o1bdd2.6
    lo1bdd2
end
