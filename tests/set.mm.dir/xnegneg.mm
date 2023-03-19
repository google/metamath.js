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
include "xnegeq.mm"
include "syl.mm"
include "renegcl.mm"
include "recn.mm"
include "negnegd.mm"
include "3eqtrd.mm"
include "xnegmnf.mm"
include "xnegpnf.mm"
include "syl6eq.mm"
include "id.mm"
include "3eqtr4a.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem xnegneg
  let cA: class A


  assert |- ( A e. RR* -> -e -e A = A )

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
    cxne
    #
    cA
    wceq
    #
    cA
    elxr
    @0
    @5
    @1
    @2
    @0
    @4
    cA
    cneg
    #
    cxne
    #
    @6
    cneg
    #
    cA
    @0
    @3
    @6
    wceq
    @4
    @7
    wceq
    cA
    rexneg
    @3
    @6
    xnegeq
    syl
    @0
    @6
    cr
    wcel
    @7
    @8
    wceq
    cA
    renegcl
    @6
    rexneg
    syl
    @0
    cA
    cA
    recn
    negnegd
    3eqtrd
    @1
    cmnf
    cxne
    #
    cpnf
    @4
    cA
    xnegmnf
    @1
    @3
    cmnf
    wceq
    @4
    @9
    wceq
    @1
    @3
    cpnf
    cxne
    #
    cmnf
    cA
    cpnf
    xnegeq
    xnegpnf
    syl6eq
    @3
    cmnf
    xnegeq
    syl
    @1
    id
    3eqtr4a
    @2
    @10
    cmnf
    @4
    cA
    xnegpnf
    @2
    @3
    cpnf
    wceq
    @4
    @10
    wceq
    @2
    @3
    @9
    cpnf
    cA
    cmnf
    xnegeq
    xnegmnf
    syl6eq
    @3
    cpnf
    xnegeq
    syl
    @2
    id
    3eqtr4a
    3jaoi
    sylbi
end
