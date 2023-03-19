include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "c0.mm"
include "df-neg.mm"
include "oveq2i.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "neg1lt0.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "0z.mm"
include "neg1z.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqtr3i.mm"

theorem risefall0lem



  assert |- ( 0 ... ( 0 - 1 ) ) = (/)

  proof
    cc0
    c1
    cneg
    #
    cfz
    co
    #
    cc0
    cc0
    c1
    cmin
    co
    #
    cfz
    co
    c0
    @0
    @2
    cc0
    cfz
    c1
    df-neg
    oveq2i
    @0
    cc0
    clt
    wbr
    #
    @1
    c0
    wceq
    #
    neg1lt0
    cc0
    cz
    wcel
    @0
    cz
    wcel
    @3
    @4
    wb
    0z
    neg1z
    cc0
    @0
    fzn
    mp2an
    mpbi
    eqtr3i
end
