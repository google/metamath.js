include "csur.mm"
include "cslt.mm"
include "wor.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "sltso.mm"
include "sotr.mm"
include "mpan.mm"

theorem slttr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. No /\ B e. No /\ C e. No ) -> ( ( A <s B /\ B <s C ) -> A <s C ) )

  proof
    csur
    cslt
    wor
    cA
    csur
    wcel
    cB
    csur
    wcel
    cC
    csur
    wcel
    w3a
    cA
    cB
    cslt
    wbr
    cB
    cC
    cslt
    wbr
    wa
    cA
    cC
    cslt
    wbr
    wi
    sltso
    csur
    cA
    cB
    cC
    cslt
    sotr
    mpan
end
