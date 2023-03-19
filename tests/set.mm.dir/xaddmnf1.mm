include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "cmnf.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "caddc.mm"
include "mnfxr.mm"
include "xaddval.mm"
include "mpan2.mm"
include "ifnefalse.mm"
include "mnfnepnf.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iftruei.mm"
include "eqtri.mm"
include "ifeq12.mm"
include "mp2an.mm"
include "ifid.mm"
include "syl6eq.mm"
include "sylan9eq.mm"

theorem xaddmnf1
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= +oo ) -> ( A +e -oo ) = -oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wne
    #
    cA
    cmnf
    cxad
    co
    #
    cA
    cpnf
    wceq
    cmnf
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
    #
    cmnf
    cpnf
    wceq
    #
    cc0
    cmnf
    cif
    #
    @6
    cpnf
    @3
    cmnf
    cA
    cmnf
    caddc
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cif
    #
    cmnf
    @0
    cmnf
    cxr
    wcel
    @2
    @12
    wceq
    mnfxr
    cA
    cmnf
    xaddval
    mpan2
    @1
    @12
    @11
    cmnf
    cA
    cpnf
    @4
    @11
    ifnefalse
    @11
    @5
    cmnf
    cmnf
    cif
    #
    cmnf
    @7
    cmnf
    wceq
    #
    @10
    cmnf
    wceq
    @11
    @13
    wceq
    cmnf
    cpnf
    wne
    #
    @14
    mnfnepnf
    cmnf
    cpnf
    cc0
    cmnf
    ifnefalse
    ax-mp
    @10
    @9
    cmnf
    @15
    @10
    @9
    wceq
    mnfnepnf
    cmnf
    cpnf
    cpnf
    @9
    ifnefalse
    ax-mp
    @3
    cmnf
    @8
    cmnf
    eqid
    iftruei
    eqtri
    @5
    @7
    cmnf
    @10
    cmnf
    ifeq12
    mp2an
    @5
    cmnf
    ifid
    eqtri
    syl6eq
    sylan9eq
end
