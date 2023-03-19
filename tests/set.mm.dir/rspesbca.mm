include "wcel.mm"
include "wsbc.mm"
include "wa.mm"
include "wsb.mm"
include "wrex.mm"
include "dfsbcq2.mm"
include "rspcev.mm"
include "cbvrexsv.mm"
include "sylibr.mm"

theorem rspesbca
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph y
  assert |- ( ( A e. B /\ [. A / x ]. ph ) -> E. x e. B ph )

  proof
    cA
    cB
    wcel
    wph
    vx
    cA
    wsbc
    #
    wa
    wph
    vx
    vy
    wsb
    #
    vy
    cB
    wrex
    wph
    vx
    cB
    wrex
    @1
    @0
    vy
    cA
    cB
    wph
    vx
    vy
    cA
    dfsbcq2
    rspcev
    wph
    vx
    vy
    cB
    cbvrexsv
    sylibr
end
