include "cuni.mm"
include "cin.mm"
include "cv.mm"
include "ciun.mm"
include "c0.mm"
include "uniiun.mm"
include "ineq1i.mm"
include "wceq.mm"
include "id.mm"
include "disjiunel.mm"
include "syl5eq.mm"

theorem disjuniel
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume disjuniel.1: |- ( ph -> Disj_ x e. A x )
  assume disjuniel.2: |- ( ph -> B C_ A )
  assume disjuniel.3: |- ( ph -> C e. ( A \ B ) )

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ph -> ( U. B i^i C ) = (/) )

  proof
    wph
    cB
    cuni
    #
    cC
    cin
    vx
    cB
    vx
    cv
    #
    ciun
    #
    cC
    cin
    c0
    @0
    @2
    cC
    vx
    cB
    uniiun
    ineq1i
    wph
    vx
    cA
    @1
    cC
    cB
    cC
    disjuniel.1
    @1
    cC
    wceq
    id
    disjuniel.2
    disjuniel.3
    disjiunel
    syl5eq
end
