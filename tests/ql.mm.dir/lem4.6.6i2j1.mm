include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "wi1.mm"
include "wi0.mm"
include "leor.mm"
include "leao1.mm"
include "lel2or.mm"
include "lear.mm"
include "lelor.mm"
include "leo.mm"
include "lerr.mm"
include "ler.mm"
include "lebi.mm"
include "df-i2.mm"
include "df-i1.mm"
include "2or.mm"
include "df-i0.mm"
include "3tr1.mm"

theorem lem4.6.6i2j1
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->2 b ) v ( a ->1 b ) ) = ( a ->0 b )

  proof
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @0
    wva
    wvb
    wa
    #
    wo
    #
    wo
    #
    @0
    wvb
    wo
    #
    wva
    wvb
    wi2
    #
    wva
    wvb
    wi1
    #
    wo
    wva
    wvb
    wi0
    @6
    @7
    @3
    @7
    @5
    wvb
    @7
    @2
    wvb
    @0
    leor
    @0
    @1
    wvb
    leao1
    lel2or
    @4
    wvb
    @0
    wva
    wvb
    lear
    lelor
    lel2or
    @0
    @6
    wvb
    @0
    @5
    @3
    @0
    @4
    leo
    lerr
    wvb
    @3
    @5
    wvb
    @2
    leo
    ler
    lel2or
    lebi
    @8
    @3
    @9
    @5
    wva
    wvb
    df-i2
    wva
    wvb
    df-i1
    2or
    wva
    wvb
    df-i0
    3tr1
end
