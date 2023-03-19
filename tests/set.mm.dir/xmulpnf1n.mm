include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cxmu.mm"
include "co.mm"
include "cxne.mm"
include "cmnf.mm"
include "wceq.mm"
include "simpl.mm"
include "pnfxr.mm"
include "xmulneg1.mm"
include "sylancl.mm"
include "xnegcl.mm"
include "adantr.mm"
include "xlt0neg1.mm"
include "biimpa.mm"
include "xmulpnf1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "xnegmnf.mm"
include "syl6eqr.mm"
include "wb.mm"
include "xmulcl.mm"
include "mnfxr.mm"
include "xneg11.mm"
include "mpbid.mm"

theorem xmulpnf1n
  let cA: class A


  assert |- ( ( A e. RR* /\ A < 0 ) -> ( A *e +oo ) = -oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    cA
    cpnf
    cxmu
    co
    #
    cxne
    #
    cmnf
    cxne
    #
    wceq
    #
    @3
    cmnf
    wceq
    #
    @2
    @4
    cpnf
    @5
    @2
    cA
    cxne
    #
    cpnf
    cxmu
    co
    #
    @4
    cpnf
    @2
    @0
    cpnf
    cxr
    wcel
    #
    @9
    @4
    wceq
    @0
    @1
    simpl
    #
    pnfxr
    cA
    cpnf
    xmulneg1
    sylancl
    @2
    @8
    cxr
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    @9
    cpnf
    wceq
    @0
    @12
    @1
    cA
    xnegcl
    adantr
    @0
    @1
    @13
    cA
    xlt0neg1
    biimpa
    @8
    xmulpnf1
    syl2anc
    eqtr3d
    xnegmnf
    syl6eqr
    @2
    @3
    cxr
    wcel
    #
    cmnf
    cxr
    wcel
    @6
    @7
    wb
    @2
    @0
    @10
    @14
    @11
    pnfxr
    cA
    cpnf
    xmulcl
    sylancl
    mnfxr
    @3
    cmnf
    xneg11
    sylancl
    mpbid
end
