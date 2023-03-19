include "wid5.mm"
include "wi1.mm"
include "wt.mm"
include "2vwomr2a.mm"
include "ax-r1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anidm.mm"
include "ran.mm"
include "lea.mm"
include "lel.mm"
include "leran.mm"
include "ler.mm"
include "ler2an.mm"
include "bltr.mm"
include "df-id5.mm"
include "lan.mm"
include "lbtr.mm"
include "lelor.mm"
include "df-i1.mm"
include "le3tr1.mm"
include "lem3.3.5lem.mm"
include "2vwomr1a.mm"

theorem lem3.4.3
  param wva: term a
  param wvb: term b
  assume lem3.4.3.1: |- ( a ->2 b ) = 1


  assert |- ( a ->2 ( a ==5 b ) ) = 1

  proof
    wva
    wva
    wvb
    wid5
    #
    wva
    @0
    wi1
    #
    wt
    wva
    wvb
    wi1
    #
    @1
    @2
    wt
    wva
    wvb
    lem3.4.3.1
    2vwomr2a
    ax-r1
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    @3
    wva
    @0
    wa
    #
    wo
    @2
    @1
    @4
    @5
    @3
    @4
    wva
    @4
    @3
    wvb
    wn
    wa
    #
    wo
    #
    wa
    #
    @5
    @4
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @8
    wva
    @9
    wvb
    @9
    wva
    wva
    anidm
    ax-r1
    ran
    @10
    wva
    @7
    @9
    wva
    wvb
    wva
    wva
    lea
    #
    lel
    @10
    @4
    @6
    @9
    wva
    wvb
    @11
    leran
    ler
    ler2an
    bltr
    @7
    @0
    wva
    @0
    @7
    wva
    wvb
    df-id5
    ax-r1
    lan
    lbtr
    lelor
    wva
    wvb
    df-i1
    wva
    @0
    df-i1
    le3tr1
    bltr
    lem3.3.5lem
    2vwomr1a
end
