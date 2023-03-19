include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "cmpt.mm"
include "eqid.mm"
include "ax-gen.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "mpteq12f.mm"
include "sylancr.mm"

theorem mpteq2da
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq2da.1: |- F/ x ph
  assume mpteq2da.2: |- ( ( ph /\ x e. A ) -> B = C )


  assert |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) )

  proof
    wph
    cA
    cA
    wceq
    #
    vx
    wal
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    vx
    cA
    cB
    cmpt
    vx
    cA
    cC
    cmpt
    wceq
    @0
    vx
    cA
    eqid
    ax-gen
    wph
    @1
    vx
    cA
    mpteq2da.1
    wph
    vx
    cv
    cA
    wcel
    @1
    mpteq2da.2
    ex
    ralrimi
    vx
    cA
    cB
    cA
    cC
    mpteq12f
    sylancr
end
