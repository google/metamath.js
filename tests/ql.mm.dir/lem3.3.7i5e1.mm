include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "wid5.mm"
include "wf.mm"
include "lear.mm"
include "lea.mm"
include "leid.mm"
include "ler2an.mm"
include "lebi.mm"
include "lecon.mm"
include "ortha.mm"
include "2or.mm"
include "ax-r5.mm"
include "or0.mm"
include "df2le2.mm"
include "ax-r1.mm"
include "3tr.mm"
include "df-i5.mm"
include "df-id5.mm"
include "3tr1.mm"

theorem lem3.3.7i5e1
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 ( a ^ b ) ) = ( a ==5 ( a ^ b ) )

  proof
    wva
    wva
    wvb
    wa
    #
    wa
    #
    wva
    wn
    #
    @0
    wa
    #
    wo
    #
    @2
    @0
    wn
    #
    wa
    #
    wo
    #
    @1
    @6
    wo
    #
    wva
    @0
    wi5
    wva
    @0
    wid5
    @7
    @0
    wf
    wo
    #
    @6
    wo
    @0
    @2
    wo
    @8
    @4
    @9
    @6
    @1
    @0
    @3
    wf
    @1
    @0
    wva
    @0
    lear
    #
    @0
    wva
    @0
    wva
    wvb
    lea
    #
    @0
    leid
    ler2an
    #
    lebi
    @2
    @0
    @0
    wva
    @11
    lecon
    #
    ortha
    2or
    ax-r5
    @9
    @0
    @6
    @2
    @0
    or0
    @2
    @5
    @13
    df2le2
    #
    2or
    @0
    @1
    @2
    @6
    @0
    @1
    @12
    @10
    lebi
    @6
    @2
    @14
    ax-r1
    2or
    3tr
    wva
    @0
    df-i5
    wva
    @0
    df-id5
    3tr1
end
