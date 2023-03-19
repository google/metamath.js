include "wn.mm"
include "wa.mm"
include "wo.mm"
include "comid.mm"
include "comcom2.mm"
include "lecom.mm"
include "fh3.mm"
include "anor3.mm"
include "lor.mm"
include "wt.mm"
include "ancom.mm"
include "df-le2.mm"
include "ax-r1.mm"
include "df-t.mm"
include "2an.mm"
include "an1.mm"
include "3tr.mm"
include "3tr2.mm"

theorem gomaex3lem1
  let wvc: term c
  let wvd: term d
  assume gomaex3lem1.3: |- c =< d '


  assert |- ( c v ( c v d ) ' ) = d '

  proof
    wvc
    wvc
    wn
    #
    wvd
    wn
    #
    wa
    #
    wo
    wvc
    @0
    wo
    #
    wvc
    @1
    wo
    #
    wa
    #
    wvc
    wvc
    wvd
    wo
    wn
    #
    wo
    @1
    wvc
    @0
    @1
    wvc
    wvc
    wvc
    comid
    comcom2
    wvc
    @1
    gomaex3lem1.3
    lecom
    fh3
    @2
    @6
    wvc
    wvc
    wvd
    anor3
    lor
    @5
    @4
    @3
    wa
    #
    @1
    wt
    wa
    #
    @1
    @3
    @4
    ancom
    @8
    @7
    @1
    @4
    wt
    @3
    @4
    @1
    wvc
    @1
    gomaex3lem1.3
    df-le2
    ax-r1
    wvc
    df-t
    2an
    ax-r1
    @1
    an1
    3tr
    3tr2
end
