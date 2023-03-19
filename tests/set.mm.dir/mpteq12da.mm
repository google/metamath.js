include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "cmpt.mm"
include "alrimi.mm"
include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"
include "mpteq12f.mm"
include "syl2anc.mm"

theorem mpteq12da
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mpteq12da.1: |- F/ x ph
  assume mpteq12da.2: |- ( ph -> A = C )
  assume mpteq12da.3: |- ( ( ph /\ x e. A ) -> B = D )


  assert |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) )

  proof
    wph
    cA
    cC
    wceq
    #
    vx
    wal
    cB
    cD
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
    cC
    cD
    cmpt
    wceq
    wph
    @0
    vx
    mpteq12da.1
    mpteq12da.2
    alrimi
    wph
    @1
    vx
    cA
    mpteq12da.1
    wph
    vx
    cv
    cA
    wcel
    @1
    mpteq12da.3
    ex
    ralrimi
    vx
    cA
    cB
    cC
    cD
    mpteq12f
    syl2anc
end
