include "wi2.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "wi0.mm"
include "df-i0.mm"
include "lbtr.mm"
include "leror.mm"
include "ax-a3.mm"
include "oridm.mm"
include "lor.mm"
include "ax-r2.mm"
include "lelan.mm"
include "oath1.mm"
include "lea.mm"
include "leor.mm"
include "ler2an.mm"
include "lebi.mm"

theorem oagen1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oagen1.1: |- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )


  assert |- ( ( a ->2 b ) ^ ( d v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( a ->2 b ) ^ ( a ->2 c ) )

  proof
    wva
    wvb
    wi2
    #
    wvd
    @0
    wva
    wvc
    wi2
    #
    wa
    #
    wo
    #
    wa
    #
    @2
    @4
    @0
    wvb
    wvc
    wo
    #
    wn
    #
    @2
    wo
    #
    wa
    @2
    @3
    @7
    @0
    @3
    @7
    @2
    wo
    #
    @7
    wvd
    @7
    @2
    wvd
    @5
    @2
    wi0
    @7
    oagen1.1
    @5
    @2
    df-i0
    lbtr
    leror
    @8
    @6
    @2
    @2
    wo
    #
    wo
    @7
    @6
    @2
    @2
    ax-a3
    @9
    @2
    @6
    @2
    oridm
    lor
    ax-r2
    lbtr
    lelan
    wva
    wvb
    wvc
    oath1
    lbtr
    @2
    @0
    @3
    @0
    @1
    lea
    @2
    wvd
    leor
    ler2an
    lebi
end
