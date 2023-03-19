include "cbigcup.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "wbr.mm"
include "eqid.mm"
include "uniex.mm"
include "brbigcup.mm"
include "mpbir.mm"
include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "wb.mm"
include "fnbigcup.mm"
include "fnbrfvb.mm"
include "mp2an.mm"

theorem fvbigcup
  let cA: class A
  assume fvbigcup.1: |- A e. _V


  assert |- ( Bigcup ` A ) = U. A

  proof
    cA
    cbigcup
    cfv
    cA
    cuni
    #
    wceq
    #
    cA
    @0
    cbigcup
    wbr
    #
    @2
    @0
    @0
    wceq
    @0
    eqid
    cA
    @0
    cA
    fvbigcup.1
    uniex
    brbigcup
    mpbir
    cbigcup
    cvv
    wfn
    cA
    cvv
    wcel
    @1
    @2
    wb
    fnbigcup
    fvbigcup.1
    cvv
    cA
    @0
    cbigcup
    fnbrfvb
    mp2an
    mpbir
end
