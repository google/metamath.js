include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clo1.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "lo1o12.mm"
include "wa.mm"
include "abscld.mm"
include "ello1mpt.mm"
include "bitrd.mm"

theorem elo1mpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vm: setvar m
  let cC: class C
  let cM: class M
  assume elo1mpt.1: |- ( ph -> A C_ RR )
  assume elo1mpt.2: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint M m
  disjoint M x
  assert |- ( ph -> ( ( x e. A |-> B ) e. O(1) <-> E. y e. RR E. m e. RR A. x e. A ( y <_ x -> ( abs ` B ) <_ m ) ) )

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
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    @0
    vm
    cv
    cle
    wbr
    wi
    vx
    cA
    wral
    vm
    cr
    wrex
    vy
    cr
    wrex
    wph
    vx
    cA
    cB
    elo1mpt.2
    lo1o12
    wph
    vx
    vy
    cA
    @0
    vm
    elo1mpt.1
    wph
    @1
    cA
    wcel
    wa
    cB
    elo1mpt.2
    abscld
    ello1mpt
    bitrd
end
