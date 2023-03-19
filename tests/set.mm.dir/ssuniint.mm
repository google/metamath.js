include "cint.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "elintd.mm"
include "elssuni.mm"
include "syl.mm"

theorem ssuniint
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume ssuniint.x: |- F/ x ph
  assume ssuniint.a: |- ( ph -> A e. V )
  assume ssuniint.b: |- ( ( ph /\ x e. B ) -> A e. x )

  disjoint A x
  disjoint B x
  assert |- ( ph -> A C_ U. |^| B )

  proof
    wph
    cA
    cB
    cint
    #
    wcel
    cA
    @0
    cuni
    wss
    wph
    vx
    cA
    cB
    cV
    ssuniint.x
    ssuniint.a
    ssuniint.b
    elintd
    cA
    @0
    elssuni
    syl
end
