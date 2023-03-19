include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i3.mm"
include "ax-a2.mm"
include "lea.mm"
include "lear.mm"
include "le2or.mm"
include "bltr.mm"
include "oridm.mm"
include "lbtr.mm"
include "sklem.mm"

theorem ska15
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->3 b ) ' v ( a ' v b ) ) = 1

  proof
    wva
    wvb
    wi3
    #
    wva
    wn
    #
    wvb
    wo
    #
    @0
    @1
    wvb
    wa
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    @2
    wa
    #
    wo
    #
    @2
    wva
    wvb
    df-i3
    @8
    @2
    @2
    wo
    @2
    @6
    @2
    @7
    @2
    @6
    @5
    @3
    wo
    @2
    @3
    @5
    ax-a2
    @5
    @1
    @3
    wvb
    @1
    @4
    lea
    @1
    wvb
    lear
    le2or
    bltr
    wva
    @2
    lear
    le2or
    @2
    oridm
    lbtr
    bltr
    sklem
end
