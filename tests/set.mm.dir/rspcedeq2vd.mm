include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "eqidd.mm"
include "rspcedvd.mm"

theorem rspcedeq2vd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rspcedeqvd.1: |- ( ph -> A e. B )
  assume rspcedeqvd.2: |- ( ( ph /\ x = A ) -> C = D )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint C x
  assert |- ( ph -> E. x e. B C = D )

  proof
    wph
    cC
    cD
    wceq
    cC
    cC
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
    #
    cD
    cC
    cC
    @0
    cC
    cD
    rspcedeqvd.2
    eqcomd
    eqeq2d
    wph
    cC
    eqidd
    rspcedvd
end
