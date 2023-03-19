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
include "wdisj.mm"
include "wceq.mm"
include "id.mm"
include "cbvdisjv.mm"
include "sylib.mm"
include "hashiun.mm"
include "cbviunv.mm"
include "a1i.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "3eqtr4d.mm"
include "syl5eq.mm"

theorem hashunif
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume hashiunf.1: |- F/ x ph
  assume hashiunf.3: |- ( ph -> A e. Fin )
  assume hashunif.4: |- ( ph -> A C_ Fin )
  assume hashunif.5: |- ( ph -> Disj_ x e. A x )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
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
    #
    cA
    @1
    chash
    cfv
    #
    vx
    csu
    #
    @0
    @2
    chash
    vx
    cA
    uniiun
    fveq2i
    wph
    vy
    cA
    vy
    cv
    #
    ciun
    #
    chash
    cfv
    cA
    @6
    chash
    cfv
    #
    vy
    csu
    #
    @3
    @5
    wph
    vy
    cA
    @6
    hashiunf.3
    wph
    cA
    cfn
    @6
    hashunif.4
    sselda
    wph
    vx
    cA
    @1
    wdisj
    vy
    cA
    @6
    wdisj
    hashunif.5
    vx
    vy
    cA
    @1
    @6
    @1
    @6
    wceq
    id
    #
    cbvdisjv
    sylib
    hashiun
    wph
    @2
    @7
    chash
    @2
    @7
    wceq
    wph
    vx
    vy
    cA
    @1
    @6
    @10
    cbviunv
    a1i
    fveq2d
    @5
    @9
    wceq
    wph
    cA
    @4
    @8
    vx
    vy
    @1
    @6
    chash
    fveq2
    cbvsumv
    a1i
    3eqtr4d
    syl5eq
end
