include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "crp.mm"
include "simpl.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "simpr.mm"
include "lttrd.mm"
include "elrpd.mm"
include "relogcl.mm"
include "syl.mm"
include "log1.mm"
include "wb.mm"
include "1rp.mm"
include "logltb.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"

theorem rplogcl
  let cA: class A


  assert |- ( ( A e. RR /\ 1 < A ) -> ( log ` A ) e. RR+ )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    cA
    clog
    cfv
    #
    @2
    cA
    crp
    wcel
    #
    @3
    cr
    wcel
    @2
    cA
    @0
    @1
    simpl
    #
    @2
    cc0
    c1
    cA
    @2
    0red
    @2
    1red
    @5
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    a1i
    @0
    @1
    simpr
    #
    lttrd
    elrpd
    #
    cA
    relogcl
    syl
    @2
    cc0
    c1
    clog
    cfv
    #
    @3
    clt
    log1
    @2
    @1
    @8
    @3
    clt
    wbr
    #
    @6
    @2
    c1
    crp
    wcel
    @4
    @1
    @9
    wb
    1rp
    @7
    c1
    cA
    logltb
    sylancr
    mpbid
    syl5eqbrr
    elrpd
end
