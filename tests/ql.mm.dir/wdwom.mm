include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "wt.mm"
include "df-i2.mm"
include "ax-r1.mm"
include "le1.mm"
include "wi5.mm"
include "df-i5.mm"
include "wi1.mm"
include "df-i1.mm"
include "ax-r2.mm"
include "wql1lem.mm"
include "wcmtr.mm"
include "or4.mm"
include "anor1.mm"
include "lor.mm"
include "ax-r5.mm"
include "or12.mm"
include "df-cmtr.mm"
include "3tr1.mm"
include "wdcom.mm"
include "skr0.mm"
include "i5lei2.mm"
include "bltr.mm"
include "lebi.mm"

theorem wdwom
  let wva: term a
  let wvb: term b
  assume wdwom.1: |- ( a ' v ( a ^ b ) ) = 1


  assert |- ( b v ( a ' ^ b ' ) ) = 1

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
    wva
    wvb
    wi2
    #
    wt
    @4
    @3
    wva
    wvb
    df-i2
    ax-r1
    @4
    wt
    @4
    le1
    wt
    wva
    wvb
    wi5
    #
    @4
    @5
    wt
    @5
    wva
    wvb
    wa
    #
    @0
    wvb
    wa
    #
    wo
    #
    @2
    wo
    #
    wt
    wva
    wvb
    df-i5
    @0
    wvb
    wo
    #
    @9
    wva
    wvb
    wva
    wvb
    wi1
    @0
    @6
    wo
    wt
    wva
    wvb
    df-i1
    wdwom.1
    ax-r2
    wql1lem
    @10
    wn
    #
    @9
    wo
    #
    wva
    wvb
    wcmtr
    #
    wt
    @8
    @11
    @2
    wo
    wo
    #
    @6
    wva
    @1
    wa
    #
    wo
    #
    @7
    @2
    wo
    #
    wo
    #
    @12
    @13
    @14
    @6
    @11
    wo
    #
    @17
    wo
    @18
    @6
    @7
    @11
    @2
    or4
    @19
    @16
    @17
    @11
    @15
    @6
    @15
    @11
    wva
    wvb
    anor1
    ax-r1
    lor
    ax-r5
    ax-r2
    @11
    @8
    @2
    or12
    wva
    wvb
    df-cmtr
    3tr1
    wva
    wvb
    wdcom
    ax-r2
    skr0
    ax-r2
    ax-r1
    wva
    wvb
    i5lei2
    bltr
    lebi
    ax-r2
end
