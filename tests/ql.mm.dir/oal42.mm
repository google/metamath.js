include "wn.mm"
include "wi2.mm"
include "wo.mm"
include "wa.mm"
include "ancom.mm"
include "u2lemanb.mm"
include "ax-r2.mm"
include "2or.mm"
include "lbtr.mm"
include "lea.mm"
include "lel2or.mm"
include "letr.mm"

theorem oal42
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume oal42.1: |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =< ( ( b ' ^ ( a ->2 b ) ) v ( c ' ^ ( a ->2 c ) ) )


  assert |- ( b ' ^ ( ( a ->2 b ) v ( ( a ->2 c ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) ) ) =< a '

  proof
    wvb
    wn
    #
    wva
    wvb
    wi2
    #
    wva
    wvc
    wi2
    #
    wvb
    wvc
    wo
    wn
    @1
    @2
    wa
    wo
    wa
    wo
    wa
    #
    wva
    wn
    #
    @0
    wa
    #
    @4
    wvc
    wn
    #
    wa
    #
    wo
    #
    @4
    @3
    @0
    @1
    wa
    #
    @6
    @2
    wa
    #
    wo
    @8
    oal42.1
    @9
    @5
    @10
    @7
    @9
    @1
    @0
    wa
    @5
    @0
    @1
    ancom
    wva
    wvb
    u2lemanb
    ax-r2
    @10
    @2
    @6
    wa
    @7
    @6
    @2
    ancom
    wva
    wvc
    u2lemanb
    ax-r2
    2or
    lbtr
    @5
    @4
    @7
    @4
    @0
    lea
    @4
    @6
    lea
    lel2or
    letr
end
