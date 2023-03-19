include "crp.mm"
include "wcel.mm"
include "ceu.mm"
include "clt.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "wb.mm"
include "epr.mm"
include "logltb.mm"
include "mpan2.mm"
include "wceq.mm"
include "loge.mm"
include "a1i.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem loglt1b
  let cA: class A


  assert |- ( A e. RR+ -> ( ( log ` A ) < 1 <-> A < _e ) )

  proof
    cA
    crp
    wcel
    #
    cA
    ceu
    clt
    wbr
    #
    cA
    clog
    cfv
    #
    ceu
    clog
    cfv
    #
    clt
    wbr
    #
    @2
    c1
    clt
    wbr
    @0
    ceu
    crp
    wcel
    @1
    @4
    wb
    epr
    cA
    ceu
    logltb
    mpan2
    @0
    @3
    c1
    @2
    clt
    @3
    c1
    wceq
    @0
    loge
    a1i
    breq2d
    bitr2d
end
