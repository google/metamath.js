include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "eqif.mm"
include "cases2.mm"
include "bitri.mm"

theorem ifval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = if ( ph , B , C ) <-> ( ( ph -> A = B ) /\ ( -. ph -> A = C ) ) )

  proof
    cA
    wph
    cB
    cC
    cif
    wceq
    wph
    cA
    cB
    wceq
    #
    wa
    wph
    wn
    #
    cA
    cC
    wceq
    #
    wa
    wo
    wph
    @0
    wi
    @1
    @2
    wi
    wa
    wph
    cA
    cB
    cC
    eqif
    wph
    @0
    @2
    cases2
    bitri
end
