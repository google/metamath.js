include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cspths.mm"
include "cpths.mm"
include "simpl.mm"
include "funres11.mm"
include "adantl.mm"
include "caddc.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "ineq2i.mm"
include "cz.mm"
include "wcel.mm"
include "0z.mm"
include "prinfzo0.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "imaeq2i.mm"
include "ima0.mm"
include "imain.mm"
include "syl5reqr.mm"
include "3jca.mm"
include "isspth.mm"
include "ispth.mm"
include "3imtr4i.mm"

theorem spthispth
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( SPaths ` G ) P -> F ( Paths ` G ) P )

  proof
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    wa
    #
    @0
    cP
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    ccnv
    wfun
    #
    cP
    cc0
    @3
    cpr
    #
    cima
    cP
    @4
    cima
    cin
    #
    c0
    wceq
    #
    w3a
    cF
    cP
    cG
    cspths
    cfv
    wbr
    cF
    cP
    cG
    cpths
    cfv
    wbr
    @2
    @0
    @5
    @8
    @0
    @1
    simpl
    @1
    @5
    @0
    @4
    cP
    funres11
    adantl
    @1
    @8
    @0
    @1
    c0
    cP
    @6
    @4
    cin
    #
    cima
    #
    @7
    @10
    cP
    c0
    cima
    c0
    @9
    c0
    cP
    @9
    @6
    cc0
    c1
    caddc
    co
    #
    @3
    cfzo
    co
    #
    cin
    #
    c0
    @4
    @12
    @6
    c1
    @11
    @3
    cfzo
    1e0p1
    oveq1i
    ineq2i
    cc0
    cz
    wcel
    @13
    c0
    wceq
    0z
    cc0
    @3
    prinfzo0
    ax-mp
    eqtri
    imaeq2i
    cP
    ima0
    eqtri
    @6
    @4
    cP
    imain
    syl5reqr
    adantl
    3jca
    cP
    cF
    cG
    isspth
    cP
    cF
    cG
    ispth
    3imtr4i
end
