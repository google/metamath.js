include "wi2.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "u2lemanb.mm"
include "anor1.mm"
include "anor3.mm"
include "3tr2.mm"
include "con1.mm"

theorem u2lemnob
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ' v b ) = ( a v b )

  proof
    wva
    wvb
    wi2
    #
    wn
    wvb
    wo
    #
    wva
    wvb
    wo
    #
    @0
    wvb
    wn
    #
    wa
    wva
    wn
    @3
    wa
    @1
    wn
    @2
    wn
    wva
    wvb
    u2lemanb
    @0
    wvb
    anor1
    wva
    wvb
    anor3
    3tr2
    con1
end
