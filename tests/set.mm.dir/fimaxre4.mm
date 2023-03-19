include "cfn.mm"
include "wcel.mm"
include "cr.mm"
include "wral.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "ex.mm"
include "ralrimi.mm"
include "fimaxre3.mm"
include "syl2anc.mm"

theorem fimaxre4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume fimaxre4.1: |- F/ x ph
  assume fimaxre4.2: |- ( ph -> A e. Fin )
  assume fimaxre4.3: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ph -> E. y e. RR A. x e. A B <_ y )

  proof
    wph
    cA
    cfn
    wcel
    cB
    cr
    wcel
    #
    vx
    cA
    wral
    cB
    vy
    cv
    cle
    wbr
    vx
    cA
    wral
    vy
    cr
    wrex
    fimaxre4.2
    wph
    @0
    vx
    cA
    fimaxre4.1
    wph
    vx
    cv
    cA
    wcel
    @0
    fimaxre4.3
    ex
    ralrimi
    vy
    vx
    cA
    cB
    fimaxre3
    syl2anc
end
