include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "wi2.mm"
include "lear.mm"
include "lel2or.mm"
include "leror.mm"
include "df-i5.mm"
include "df-i2.mm"
include "le3tr1.mm"

theorem i5lei2
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 b ) =< ( a ->2 b )

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
    wn
    wa
    #
    wo
    wvb
    @4
    wo
    wva
    wvb
    wi5
    wva
    wvb
    wi2
    @3
    wvb
    @4
    @0
    wvb
    @2
    wva
    wvb
    lear
    @1
    wvb
    lear
    lel2or
    leror
    wva
    wvb
    df-i5
    wva
    wvb
    df-i2
    le3tr1
end
