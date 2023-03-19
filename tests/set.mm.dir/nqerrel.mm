include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "cerq.mm"
include "cfv.mm"
include "wbr.mm"
include "ceq.mm"
include "wceq.mm"
include "eqid.mm"
include "wfn.mm"
include "wb.mm"
include "cnq.mm"
include "wf.mm"
include "nqerf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnbrfvb.mm"
include "mpan.mm"
include "mpbii.mm"
include "cin.mm"
include "df-erq.mm"
include "inss1.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "syl.mm"

theorem nqerrel
  let cA: class A


  assert |- ( A e. ( N. X. N. ) -> A ~Q ( /Q ` A ) )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cA
    cA
    cerq
    cfv
    #
    cerq
    wbr
    #
    cA
    @2
    ceq
    wbr
    @1
    @2
    @2
    wceq
    #
    @3
    @2
    eqid
    cerq
    @0
    wfn
    #
    @1
    @4
    @3
    wb
    @0
    cnq
    cerq
    wf
    @5
    nqerf
    @0
    cnq
    cerq
    ffn
    ax-mp
    @0
    cA
    @2
    cerq
    fnbrfvb
    mpan
    mpbii
    cerq
    ceq
    cA
    @2
    cerq
    ceq
    @0
    cnq
    cxp
    #
    cin
    ceq
    df-erq
    ceq
    @6
    inss1
    eqsstri
    ssbri
    syl
end
