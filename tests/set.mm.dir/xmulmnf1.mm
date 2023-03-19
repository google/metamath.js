include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmnf.mm"
include "cxmu.mm"
include "co.mm"
include "cpnf.mm"
include "cxne.mm"
include "xnegpnf.mm"
include "oveq2i.mm"
include "wceq.mm"
include "simpl.mm"
include "pnfxr.mm"
include "xmulneg2.mm"
include "sylancl.mm"
include "xmulpnf1.mm"
include "xnegeq.mm"
include "syl.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "syl5eqr.mm"

theorem xmulmnf1
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 < A ) -> ( A *e -oo ) = -oo )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cA
    cmnf
    cxmu
    co
    cA
    cpnf
    cxne
    #
    cxmu
    co
    #
    cmnf
    @3
    cmnf
    cA
    cxmu
    xnegpnf
    oveq2i
    @2
    @4
    cA
    cpnf
    cxmu
    co
    #
    cxne
    #
    cmnf
    @2
    @0
    cpnf
    cxr
    wcel
    @4
    @6
    wceq
    @0
    @1
    simpl
    pnfxr
    cA
    cpnf
    xmulneg2
    sylancl
    @2
    @6
    @3
    cmnf
    @2
    @5
    cpnf
    wceq
    @6
    @3
    wceq
    cA
    xmulpnf1
    @5
    cpnf
    xnegeq
    syl
    xnegpnf
    syl6eq
    eqtrd
    syl5eqr
end
