include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i1.mm"
include "ax-r5.mm"
include "or32.mm"
include "oridm.mm"
include "ax-r2.mm"

theorem u1lemona
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) v a ' ) = ( a ' v ( a ^ b ) )

  proof
    wva
    wvb
    wi1
    #
    wva
    wn
    #
    wo
    @1
    wva
    wvb
    wa
    #
    wo
    #
    @1
    wo
    #
    @3
    @0
    @3
    @1
    wva
    wvb
    df-i1
    ax-r5
    @4
    @1
    @1
    wo
    #
    @2
    wo
    @3
    @1
    @2
    @1
    or32
    @5
    @1
    @2
    @1
    oridm
    ax-r5
    ax-r2
    ax-r2
end
