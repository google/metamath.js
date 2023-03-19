include "c1.mm"
include "cppi.mm"
include "cfv.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "cc0.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "1z.mm"
include "ppival2.mm"
include "ax-mp.mm"
include "c0.mm"
include "clt.mm"
include "wbr.mm"
include "1lt2.mm"
include "wb.mm"
include "2z.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "ineq1i.mm"
include "0in.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "hash0.mm"

theorem ppi1



  assert |- ( ppi ` 1 ) = 0

  proof
    c1
    cppi
    cfv
    #
    c2
    c1
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    cc0
    c1
    cz
    wcel
    #
    @0
    @3
    wceq
    1z
    c1
    ppival2
    ax-mp
    @3
    c0
    chash
    cfv
    cc0
    @2
    c0
    chash
    @2
    c0
    cprime
    cin
    c0
    @1
    c0
    cprime
    c1
    c2
    clt
    wbr
    #
    @1
    c0
    wceq
    #
    1lt2
    c2
    cz
    wcel
    @4
    @5
    @6
    wb
    2z
    1z
    c2
    c1
    fzn
    mp2an
    mpbi
    ineq1i
    cprime
    0in
    eqtri
    fveq2i
    hash0
    eqtri
    eqtri
end
