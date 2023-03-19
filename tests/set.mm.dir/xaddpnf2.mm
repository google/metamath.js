include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "cpnf.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "pnfxr.mm"
include "xaddval.mm"
include "mpan.mm"
include "eqid.mm"
include "iftruei.mm"
include "ifnefalse.mm"
include "syl5eq.mm"
include "sylan9eq.mm"

theorem xaddpnf2
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= -oo ) -> ( +oo +e A ) = +oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    cpnf
    cA
    cxad
    co
    #
    cpnf
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cpnf
    cmnf
    wceq
    cA
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    @6
    cpnf
    @4
    cmnf
    cpnf
    cA
    caddc
    co
    cif
    cif
    cif
    #
    cif
    #
    cpnf
    cpnf
    cxr
    wcel
    @0
    @2
    @8
    wceq
    pnfxr
    cpnf
    cA
    xaddval
    mpan
    @1
    @8
    @5
    cpnf
    @3
    @5
    @7
    cpnf
    eqid
    iftruei
    cA
    cmnf
    cc0
    cpnf
    ifnefalse
    syl5eq
    sylan9eq
end
