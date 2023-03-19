include "wss.mm"
include "cmpt.mm"
include "cres.mm"
include "wceq.mm"
include "resmpt.mm"
include "syl.mm"

theorem resmptd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume resmptd.b: |- ( ph -> B C_ A )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C ) )

  proof
    wph
    cB
    cA
    wss
    vx
    cA
    cC
    cmpt
    cB
    cres
    vx
    cB
    cC
    cmpt
    wceq
    resmptd.b
    vx
    cA
    cB
    cC
    resmpt
    syl
end
