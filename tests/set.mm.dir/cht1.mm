include "c1.mm"
include "ccht.mm"
include "cfv.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "c0.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "1re.mm"
include "chtval.mm"
include "ax-mp.mm"
include "c2.mm"
include "cfl.mm"
include "cfz.mm"
include "ppisval.mm"
include "cz.mm"
include "1z.mm"
include "flid.mm"
include "oveq2i.mm"
include "clt.mm"
include "wbr.mm"
include "1lt2.mm"
include "wb.mm"
include "2z.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqtri.mm"
include "ineq1i.mm"
include "0in.mm"
include "3eqtri.mm"
include "sumeq1i.mm"
include "sum0.mm"

theorem cht1
  let vp: setvar p


  assert |- ( theta ` 1 ) = 0

  proof
    c1
    ccht
    cfv
    #
    cc0
    c1
    cicc
    co
    cprime
    cin
    #
    vp
    cv
    clog
    cfv
    #
    vp
    csu
    #
    c0
    @2
    vp
    csu
    cc0
    c1
    cr
    wcel
    #
    @0
    @3
    wceq
    1re
    c1
    vp
    chtval
    ax-mp
    @1
    c0
    @2
    vp
    @1
    c2
    c1
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    c0
    cprime
    cin
    c0
    @4
    @1
    @7
    wceq
    1re
    c1
    ppisval
    ax-mp
    @6
    c0
    cprime
    @6
    c2
    c1
    cfz
    co
    #
    c0
    @5
    c1
    c2
    cfz
    c1
    cz
    wcel
    #
    @5
    c1
    wceq
    1z
    c1
    flid
    ax-mp
    oveq2i
    c1
    c2
    clt
    wbr
    #
    @8
    c0
    wceq
    #
    1lt2
    c2
    cz
    wcel
    @9
    @10
    @11
    wb
    2z
    1z
    c2
    c1
    fzn
    mp2an
    mpbi
    eqtri
    ineq1i
    cprime
    0in
    3eqtri
    sumeq1i
    @2
    vp
    sum0
    3eqtri
end
