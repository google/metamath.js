include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "cxne.mm"
include "elxr.mm"
include "cneg.mm"
include "rexneg.mm"
include "renegcl.mm"
include "eqeltrd.mm"
include "rexrd.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "mnfxr.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "xnegmnf.mm"
include "pnfxr.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem xnegcl
  let cA: class A


  assert |- ( A e. RR* -> -e A e. RR* )

  proof
    cA
    cxr
    wcel
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cA
    cxne
    #
    cxr
    wcel
    #
    cA
    elxr
    @0
    @4
    @1
    @2
    @0
    @3
    @0
    @3
    cA
    cneg
    cr
    cA
    rexneg
    cA
    renegcl
    eqeltrd
    rexrd
    @1
    @3
    cpnf
    cxne
    #
    cxr
    cA
    cpnf
    xnegeq
    @5
    cmnf
    cxr
    xnegpnf
    mnfxr
    eqeltri
    syl6eqel
    @2
    @3
    cmnf
    cxne
    #
    cxr
    cA
    cmnf
    xnegeq
    @6
    cpnf
    cxr
    xnegmnf
    pnfxr
    eqeltri
    syl6eqel
    3jaoi
    sylbi
end
