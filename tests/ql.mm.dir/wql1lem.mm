include "wn.mm"
include "wo.mm"
include "wt.mm"
include "le1.mm"
include "wi1.mm"
include "ax-r1.mm"
include "wa.mm"
include "df-i1.mm"
include "lear.mm"
include "lelor.mm"
include "bltr.mm"
include "lebi.mm"

theorem wql1lem
  let wva: term a
  let wvb: term b
  assume wql1lem.1: |- ( a ->1 b ) = 1


  assert |- ( a ' v b ) = 1

  proof
    wva
    wn
    #
    wvb
    wo
    #
    wt
    @1
    le1
    wt
    wva
    wvb
    wi1
    #
    @1
    @2
    wt
    wql1lem.1
    ax-r1
    @2
    @0
    wva
    wvb
    wa
    #
    wo
    @1
    wva
    wvb
    df-i1
    @3
    wvb
    @0
    wva
    wvb
    lear
    lelor
    bltr
    bltr
    lebi
end
