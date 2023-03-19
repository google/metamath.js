include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "neanior.mm"
include "elpri.mm"
include "con3i.mm"
include "sylbi.mm"
include "syl2anc.mm"

theorem nelprd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume nelprd.1: |- ( ph -> A =/= B )
  assume nelprd.2: |- ( ph -> A =/= C )


  assert |- ( ph -> -. A e. { B , C } )

  proof
    wph
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cA
    cB
    cC
    cpr
    wcel
    #
    wn
    #
    nelprd.1
    nelprd.2
    @0
    @1
    wa
    cA
    cB
    wceq
    cA
    cC
    wceq
    wo
    #
    wn
    @3
    cA
    cB
    cA
    cC
    neanior
    @2
    @4
    cA
    cB
    cC
    elpri
    con3i
    sylbi
    syl2anc
end
