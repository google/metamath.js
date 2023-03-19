include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "wb.mm"
include "df-sbc.mm"
include "a1i.mm"
include "eleq2i.mm"
include "syl6rbbr.mm"

theorem bnj1454
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bnj1454.1: |- A = { x | ph }


  assert |- ( B e. _V -> ( B e. A <-> [. B / x ]. ph ) )

  proof
    cB
    cvv
    wcel
    #
    wph
    vx
    cB
    wsbc
    #
    cB
    wph
    vx
    cab
    #
    wcel
    #
    cB
    cA
    wcel
    @1
    @3
    wb
    @0
    wph
    vx
    cB
    df-sbc
    a1i
    cA
    @2
    cB
    bnj1454.1
    eleq2i
    syl6rbbr
end
