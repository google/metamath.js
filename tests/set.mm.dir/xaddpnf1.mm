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
include "mpan2.mm"
include "pnfnemnf.mm"
include "ifnefalse.mm"
include "mp1i.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "ifeq12d.mm"
include "ifid.mm"
include "sylan9eq.mm"

theorem xaddpnf1
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= -oo ) -> ( A +e +oo ) = +oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    cA
    cpnf
    cxad
    co
    #
    cA
    cpnf
    wceq
    #
    cpnf
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cA
    cmnf
    wceq
    cpnf
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @6
    cpnf
    @4
    cmnf
    cA
    cpnf
    caddc
    co
    cif
    #
    cif
    #
    cif
    #
    cif
    #
    cpnf
    @0
    cpnf
    cxr
    wcel
    @2
    @11
    wceq
    pnfxr
    cA
    cpnf
    xaddval
    mpan2
    @1
    @11
    @3
    cpnf
    cpnf
    cif
    cpnf
    @1
    @3
    @5
    cpnf
    @10
    cpnf
    cpnf
    cmnf
    wne
    @5
    cpnf
    wceq
    @1
    pnfnemnf
    cpnf
    cmnf
    cc0
    cpnf
    ifnefalse
    mp1i
    @1
    @10
    @9
    cpnf
    cA
    cmnf
    @7
    @9
    ifnefalse
    @6
    cpnf
    @8
    cpnf
    eqid
    iftruei
    syl6eq
    ifeq12d
    @3
    cpnf
    ifid
    syl6eq
    sylan9eq
end
