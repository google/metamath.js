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
include "mpan.mm"
include "mnfnepnf.mm"
include "ifnefalse.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iftruei.mm"
include "eqtri.mm"
include "syl5eq.mm"
include "sylan9eq.mm"

theorem xaddmnf2
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= +oo ) -> ( -oo +e A ) = -oo )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wne
    #
    cmnf
    cA
    cxad
    co
    #
    cmnf
    cpnf
    wceq
    cA
    cmnf
    wceq
    #
    cc0
    cpnf
    cif
    #
    cmnf
    cmnf
    wceq
    #
    cA
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
    cmnf
    cA
    caddc
    co
    cif
    cif
    #
    cif
    #
    cif
    #
    cmnf
    cmnf
    cxr
    wcel
    @0
    @2
    @10
    wceq
    mnfxr
    cmnf
    cA
    xaddval
    mpan
    @1
    @10
    @7
    cmnf
    @10
    @9
    @7
    cmnf
    cpnf
    wne
    @10
    @9
    wceq
    mnfnepnf
    cmnf
    cpnf
    @4
    @9
    ifnefalse
    ax-mp
    @5
    @7
    @8
    cmnf
    eqid
    iftruei
    eqtri
    cA
    cpnf
    cc0
    cmnf
    ifnefalse
    syl5eq
    sylan9eq
end
