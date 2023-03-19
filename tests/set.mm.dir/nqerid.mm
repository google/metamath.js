include "cerq.mm"
include "wfun.mm"
include "cnq.mm"
include "wcel.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "cnpi.mm"
include "cxp.mm"
include "wf.mm"
include "nqerf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "ceq.mm"
include "elpqn.mm"
include "id.mm"
include "wer.mm"
include "enqer.mm"
include "a1i.mm"
include "erref.mm"
include "cin.mm"
include "w3a.mm"
include "df-erq.mm"
include "breqi.mm"
include "brinxp2.mm"
include "bitri.mm"
include "syl3anbrc.mm"
include "funbrfv.mm"
include "mpsyl.mm"

theorem nqerid
  let cA: class A


  assert |- ( A e. Q. -> ( /Q ` A ) = A )

  proof
    cerq
    wfun
    #
    cA
    cnq
    wcel
    #
    cA
    cA
    cerq
    wbr
    #
    cA
    cerq
    cfv
    cA
    wceq
    cnpi
    cnpi
    cxp
    #
    cnq
    cerq
    wf
    @0
    nqerf
    @3
    cnq
    cerq
    ffun
    ax-mp
    @1
    cA
    @3
    wcel
    #
    @1
    cA
    cA
    ceq
    wbr
    #
    @2
    cA
    elpqn
    #
    @1
    id
    @1
    cA
    ceq
    @3
    @3
    ceq
    wer
    @1
    enqer
    a1i
    @6
    erref
    @2
    cA
    cA
    ceq
    @3
    cnq
    cxp
    cin
    #
    wbr
    @4
    @1
    @5
    w3a
    cA
    cA
    cerq
    @7
    df-erq
    breqi
    cA
    cA
    @3
    cnq
    ceq
    brinxp2
    bitri
    syl3anbrc
    cA
    cA
    cerq
    funbrfv
    mpsyl
end
