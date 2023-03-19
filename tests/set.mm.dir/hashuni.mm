include "cuni.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "csu.mm"
include "uniiun.mm"
include "fveq2i.mm"
include "cfn.mm"
include "sselda.mm"
include "hashiun.mm"
include "syl5eq.mm"

theorem hashuni
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume hashuni.1: |- ( ph -> A e. Fin )
  assume hashuni.2: |- ( ph -> A C_ Fin )
  assume hashuni.3: |- ( ph -> Disj_ x e. A x )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( # ` U. A ) = sum_ x e. A ( # ` x ) )

  proof
    wph
    cA
    cuni
    #
    chash
    cfv
    vx
    cA
    vx
    cv
    #
    ciun
    #
    chash
    cfv
    cA
    @1
    chash
    cfv
    vx
    csu
    @0
    @2
    chash
    vx
    cA
    uniiun
    fveq2i
    wph
    vx
    cA
    @1
    hashuni.1
    wph
    cA
    cfn
    @1
    hashuni.2
    sselda
    hashuni.3
    hashiun
    syl5eq
end
