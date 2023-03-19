include "wn.mm"
include "wa.mm"
include "wo.mm"
include "comid.mm"
include "comcom2.mm"
include "fh3.mm"
include "lear.mm"
include "ax-a4.mm"
include "df-le1.mm"
include "leid.mm"
include "ler2an.mm"
include "lebi.mm"
include "ax-r2.mm"

theorem com3iia
  param wva: term a
  param wvb: term b
  assume com3iia.1: |- a C b


  assert |- ( a v ( a ' ^ b ) ) = ( a v b )

  proof
    wva
    wva
    wn
    #
    wvb
    wa
    wo
    wva
    @0
    wo
    #
    wva
    wvb
    wo
    #
    wa
    #
    @2
    wva
    @0
    wvb
    wva
    wva
    wva
    comid
    comcom2
    com3iia.1
    fh3
    @3
    @2
    @1
    @2
    lear
    @2
    @1
    @2
    @2
    @1
    @2
    wva
    ax-a4
    df-le1
    @2
    leid
    ler2an
    lebi
    ax-r2
end
