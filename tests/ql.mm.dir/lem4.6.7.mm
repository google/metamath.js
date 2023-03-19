include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "wt.mm"
include "leid.mm"
include "sklem.mm"
include "ax-r1.mm"
include "df-le2.mm"
include "2an.mm"
include "ax-a3.mm"
include "le1.mm"
include "ler2an.mm"
include "lel2or.mm"
include "leran.mm"
include "leao2.mm"
include "ler.mm"
include "lebi.mm"
include "ax-r2.mm"
include "comid.mm"
include "comcom3.mm"
include "lecom.mm"
include "fh3.mm"
include "3tr1.mm"
include "df-le1.mm"
include "df-i1.mm"
include "lbtr.mm"

theorem lem4.6.7
  param wva: term a
  param wvb: term b
  assume lem4.6.7.1: |- a ' =< b


  assert |- b =< ( a ->1 b )

  proof
    wvb
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wva
    wvb
    wi1
    #
    wvb
    @2
    wt
    wvb
    wa
    #
    @0
    wva
    wo
    #
    @0
    wvb
    wo
    #
    wa
    wvb
    @2
    wo
    #
    @2
    wt
    @5
    wvb
    @6
    @5
    wt
    wva
    wva
    wva
    leid
    sklem
    ax-r1
    @6
    wvb
    @0
    wvb
    lem4.6.7.1
    df-le2
    ax-r1
    2an
    @7
    wvb
    @0
    wo
    #
    @1
    wo
    #
    @4
    @9
    @7
    wvb
    @0
    @1
    ax-a3
    ax-r1
    @9
    @4
    @8
    @4
    @1
    wvb
    @4
    @0
    wvb
    wt
    wvb
    wvb
    le1
    wvb
    leid
    ler2an
    @0
    wt
    wvb
    @0
    le1
    lem4.6.7.1
    ler2an
    lel2or
    wva
    wt
    wvb
    wva
    le1
    leran
    lel2or
    @4
    @8
    @1
    wvb
    wt
    @0
    leao2
    ler
    lebi
    ax-r2
    @0
    wva
    wvb
    wva
    wva
    wva
    comid
    comcom3
    @0
    wvb
    lem4.6.7.1
    lecom
    fh3
    3tr1
    df-le1
    @3
    @2
    wva
    wvb
    df-i1
    ax-r1
    lbtr
end
