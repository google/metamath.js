include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "wi.mm"
include "wa.mm"
include "cun.mm"
include "simpr.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "wb.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "wn.mm"
include "difsn.mm"
include "biimpd.mm"
include "pm2.61i.mm"

theorem difsnexi
  let cK: class K
  let cN: class N


  assert |- ( ( N \ { K } ) e. _V -> N e. _V )

  proof
    cK
    cN
    wcel
    #
    cN
    cK
    csn
    #
    cdif
    #
    cvv
    wcel
    #
    cN
    cvv
    wcel
    #
    wi
    @0
    @3
    @4
    @0
    @3
    wa
    #
    @4
    @2
    @1
    cun
    #
    cvv
    wcel
    #
    @5
    @3
    @1
    cvv
    wcel
    @7
    @0
    @3
    simpr
    cK
    snex
    @2
    @1
    cvv
    cvv
    unexg
    sylancl
    @0
    @4
    @7
    wb
    @3
    @0
    cN
    @6
    cvv
    @0
    @6
    cN
    cN
    cK
    difsnid
    eqcomd
    eleq1d
    adantr
    mpbird
    ex
    @0
    wn
    #
    @3
    @4
    @8
    @2
    cN
    cvv
    cK
    cN
    difsn
    eleq1d
    biimpd
    pm2.61i
end
