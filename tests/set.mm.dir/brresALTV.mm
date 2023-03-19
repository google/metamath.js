include "wcel.mm"
include "cop.mm"
include "cres.mm"
include "wa.mm"
include "wbr.mm"
include "opelresALTV.mm"
include "df-br.mm"
include "anbi2i.mm"
include "3bitr4g.mm"

theorem brresALTV
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V


  assert |- ( C e. V -> ( B ( R |` A ) C <-> ( B e. A /\ B R C ) ) )

  proof
    cC
    cV
    wcel
    cB
    cC
    cop
    #
    cR
    cA
    cres
    #
    wcel
    cB
    cA
    wcel
    #
    @0
    cR
    wcel
    #
    wa
    cB
    cC
    @1
    wbr
    @2
    cB
    cC
    cR
    wbr
    #
    wa
    cA
    cB
    cC
    cR
    cV
    opelresALTV
    cB
    cC
    @1
    df-br
    @4
    @3
    @2
    cB
    cC
    cR
    df-br
    anbi2i
    3bitr4g
end
