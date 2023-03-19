include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "eqeq1d.mm"
include "eqidd.mm"
include "rspcedvd.mm"

theorem rspcedeq1vd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rspcedeqvd.1: |- ( ph -> A e. B )
  assume rspcedeqvd.2: |- ( ( ph /\ x = A ) -> C = D )

  disjoint D x
  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> E. x e. B C = D )

  proof
    wph
    cC
    cD
    wceq
    cD
    cD
    wceq
    vx
    cA
    cB
    rspcedeqvd.1
    wph
    vx
    cv
    cA
    wceq
    wa
    cC
    cD
    cD
    rspcedeqvd.2
    eqeq1d
    wph
    cD
    eqidd
    rspcedvd
end
