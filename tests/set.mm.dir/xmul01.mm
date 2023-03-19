include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "wa.mm"
include "cmnf.mm"
include "cmul.mm"
include "cif.mm"
include "0xr.mm"
include "xmulval.mm"
include "mpan2.mm"
include "eqid.mm"
include "olci.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem xmul01
  let cA: class A


  assert |- ( A e. RR* -> ( A *e 0 ) = 0 )

  proof
    cA
    cxr
    wcel
    #
    cA
    cc0
    cxmu
    co
    #
    cA
    cc0
    wceq
    #
    cc0
    cc0
    wceq
    #
    wo
    #
    cc0
    cc0
    cc0
    clt
    wbr
    #
    cA
    cpnf
    wceq
    wa
    #
    @5
    cA
    cmnf
    wceq
    wa
    #
    wo
    cc0
    cA
    clt
    wbr
    #
    cc0
    cpnf
    wceq
    #
    wa
    cA
    cc0
    clt
    wbr
    #
    cc0
    cmnf
    wceq
    #
    wa
    wo
    wo
    cpnf
    @7
    @6
    wo
    @8
    @11
    wa
    @10
    @9
    wa
    wo
    wo
    cmnf
    cA
    cc0
    cmul
    co
    cif
    cif
    #
    cif
    #
    cc0
    @0
    cc0
    cxr
    wcel
    @1
    @13
    wceq
    0xr
    cA
    cc0
    xmulval
    mpan2
    @4
    cc0
    @12
    @3
    @2
    cc0
    eqid
    olci
    iftruei
    syl6eq
end
