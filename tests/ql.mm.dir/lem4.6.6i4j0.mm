include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "wi0.mm"
include "leao4.mm"
include "leao1.mm"
include "lel2or.mm"
include "lea.mm"
include "df-le2.mm"
include "df-i4.mm"
include "df-i0.mm"
include "2or.mm"
include "3tr1.mm"

theorem lem4.6.6i4j0
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) v ( a ->0 b ) ) = ( a ->0 b )

  proof
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wo
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @4
    wo
    @4
    wva
    wvb
    wi4
    #
    wva
    wvb
    wi0
    #
    wo
    @9
    @7
    @4
    @3
    @4
    @6
    @0
    @4
    @2
    wvb
    wva
    @1
    leao4
    @1
    wvb
    wvb
    leao1
    lel2or
    @4
    @5
    lea
    lel2or
    df-le2
    @8
    @7
    @9
    @4
    wva
    wvb
    df-i4
    wva
    wvb
    df-i0
    #
    2or
    @10
    3tr1
end
