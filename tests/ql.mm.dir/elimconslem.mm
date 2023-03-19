include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "df-t.mm"
include "lecon.mm"
include "oran3.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "lelor.mm"
include "bltr.mm"
include "lelan.mm"
include "an1.mm"
include "comor1.mm"
include "comcom7.mm"
include "df-a.mm"
include "lecom.mm"
include "comcom6.mm"
include "fh2c.mm"
include "le3tr2.mm"
include "wi1.mm"
include "df-i1.mm"
include "3tr2.mm"
include "lor.mm"
include "ax-r4.mm"
include "3tr1.mm"
include "lear.mm"
include "leror.mm"
include "letr.mm"
include "ax-a2.mm"
include "leao1.mm"
include "df-le2.mm"
include "ax-r2.mm"

theorem elimconslem
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume elimcons.1: |- ( a ->1 c ) = ( b ->1 c )
  assume elimcons.2: |- ( a ^ c ) =< ( b v c ' )


  assert |- a =< ( b v c ' )

  proof
    wva
    wvb
    wvc
    wn
    #
    wo
    #
    wvb
    wvb
    wn
    #
    @0
    wo
    #
    wa
    #
    wo
    #
    @1
    wva
    wva
    @1
    wa
    #
    @4
    wo
    #
    @5
    wva
    @6
    wva
    wva
    wn
    #
    @0
    wo
    #
    wa
    #
    wo
    #
    @7
    wva
    wt
    wa
    wva
    @1
    @9
    wo
    #
    wa
    wva
    @11
    wt
    @12
    wva
    wt
    @1
    @1
    wn
    #
    wo
    @12
    @1
    df-t
    @13
    @9
    @1
    @13
    wva
    wvc
    wa
    #
    wn
    #
    @9
    @14
    @1
    elimcons.2
    lecon
    @9
    @15
    wva
    wvc
    oran3
    ax-r1
    lbtr
    lelor
    bltr
    lelan
    wva
    an1
    @9
    wva
    @1
    @9
    wva
    @8
    @0
    comor1
    comcom7
    @9
    @1
    @9
    wn
    #
    @1
    @16
    @14
    @1
    @14
    @16
    wva
    wvc
    df-a
    #
    ax-r1
    elimcons.2
    bltr
    lecom
    comcom6
    fh2c
    le3tr2
    @10
    @4
    @6
    @8
    @16
    wo
    #
    wn
    @2
    @3
    wn
    #
    wo
    #
    wn
    @10
    @4
    @18
    @20
    @8
    @14
    wo
    #
    @2
    wvb
    wvc
    wa
    #
    wo
    #
    @18
    @20
    wva
    wvc
    wi1
    wvb
    wvc
    wi1
    @21
    @23
    elimcons.1
    wva
    wvc
    df-i1
    wvb
    wvc
    df-i1
    3tr2
    @14
    @16
    @8
    @17
    lor
    @22
    @19
    @2
    wvb
    wvc
    df-a
    lor
    3tr2
    ax-r4
    wva
    @9
    df-a
    wvb
    @3
    df-a
    3tr1
    lor
    lbtr
    @6
    @1
    @4
    wva
    @1
    lear
    leror
    letr
    @5
    @4
    @1
    wo
    @1
    @1
    @4
    ax-a2
    @4
    @1
    wvb
    @3
    @0
    leao1
    df-le2
    ax-r2
    lbtr
end
