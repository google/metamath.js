include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wne.mm"
include "0ne1.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "c0ex.mm"
include "1ex.mm"
include "wa.mm"
include "hashprg.mm"
include "bicomd.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem prhash2ex



  assert |- ( # ` { 0 , 1 } ) = 2

  proof
    cc0
    c1
    cpr
    chash
    cfv
    c2
    wceq
    #
    cc0
    c1
    wne
    #
    0ne1
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    @0
    @1
    wb
    c0ex
    1ex
    @2
    @3
    wa
    @1
    @0
    cc0
    c1
    cvv
    cvv
    hashprg
    bicomd
    mp2an
    mpbir
end
