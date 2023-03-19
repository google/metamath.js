include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "cc0.mm"
include "wb.mm"
include "1rp.mm"
include "logltb.mm"
include "mpan.mm"
include "wceq.mm"
include "log1.mm"
include "a1i.mm"
include "breq1d.mm"
include "bitr2d.mm"

theorem loggt0b
  let cA: class A


  assert |- ( A e. RR+ -> ( 0 < ( log ` A ) <-> 1 < A ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    c1
    clog
    cfv
    #
    cA
    clog
    cfv
    #
    clt
    wbr
    #
    cc0
    @3
    clt
    wbr
    c1
    crp
    wcel
    @0
    @1
    @4
    wb
    1rp
    c1
    cA
    logltb
    mpan
    @0
    @2
    cc0
    @3
    clt
    @2
    cc0
    wceq
    @0
    log1
    a1i
    breq1d
    bitr2d
end
