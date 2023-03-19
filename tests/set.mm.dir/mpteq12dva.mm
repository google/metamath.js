include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "cmpt.mm"
include "alrimiv.mm"
include "ralrimiva.mm"
include "mpteq12f.mm"
include "syl2anc.mm"

theorem mpteq12dva
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume mpteq12dv.1: |- ( ph -> A = C )
  assume mpteq12dva.2: |- ( ( ph /\ x e. A ) -> B = D )

  disjoint ph x
  disjoint x y
  disjoint ph y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
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
    mpteq12dv.1
    alrimiv
    wph
    @1
    vx
    cA
    mpteq12dva.2
    ralrimiva
    vx
    cA
    cB
    cC
    cD
    mpteq12f
    syl2anc
end
