include "wo.mm"
include "wn.mm"
include "wt.mm"
include "wa.mm"
include "lecon3.mm"
include "lecom.mm"
include "comid.mm"
include "comcom2.mm"
include "fh3r.mm"
include "anor3.mm"
include "ax-r5.mm"
include "ax-r1.mm"
include "anabs.mm"
include "df2le1.mm"
include "leid.mm"
include "lel2or.mm"
include "lebi.mm"
include "df-t.mm"
include "ax-a2.mm"
include "ax-r2.mm"
include "2an.mm"
include "3tr1.mm"
include "an1.mm"

theorem gomaex3lem2
  param wve: term e
  param wvf: term f
  assume gomaex3lem2.5: |- e =< f '


  assert |- ( ( e v f ) ' v f ) = e '

  proof
    wve
    wvf
    wo
    wn
    #
    wvf
    wo
    #
    wve
    wn
    #
    wt
    wa
    #
    @2
    @2
    wvf
    wn
    #
    wa
    #
    wvf
    wo
    #
    @2
    wvf
    wo
    #
    @4
    wvf
    wo
    #
    wa
    @1
    @3
    wvf
    @2
    @4
    wvf
    @2
    wve
    wvf
    gomaex3lem2.5
    lecon3
    #
    lecom
    wvf
    wvf
    wvf
    comid
    comcom2
    fh3r
    @6
    @1
    @5
    @0
    wvf
    wve
    wvf
    anor3
    ax-r5
    ax-r1
    @2
    @7
    wt
    @8
    @2
    @7
    @2
    @7
    @2
    wvf
    anabs
    df2le1
    @2
    @2
    wvf
    @2
    leid
    @9
    lel2or
    lebi
    wt
    wvf
    @4
    wo
    @8
    wvf
    df-t
    wvf
    @4
    ax-a2
    ax-r2
    2an
    3tr1
    @2
    an1
    ax-r2
end
