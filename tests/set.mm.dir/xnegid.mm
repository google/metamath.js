include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "elxr.mm"
include "cneg.mm"
include "caddc.mm"
include "rexneg.mm"
include "oveq2d.mm"
include "renegcl.mm"
include "rexadd.mm"
include "mpdan.mm"
include "recn.mm"
include "negidd.mm"
include "3eqtrd.mm"
include "id.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "pnfaddmnf.mm"
include "xnegmnf.mm"
include "mnfaddpnf.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem xnegid
  let cA: class A


  assert |- ( A e. RR* -> ( A +e -e A ) = 0 )

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
    cA
    cxne
    #
    cxad
    co
    #
    cc0
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
    cA
    cneg
    #
    cxad
    co
    #
    cA
    @6
    caddc
    co
    #
    cc0
    @0
    @3
    @6
    cA
    cxad
    cA
    rexneg
    oveq2d
    @0
    @6
    cr
    wcel
    @7
    @8
    wceq
    cA
    renegcl
    cA
    @6
    rexadd
    mpdan
    @0
    cA
    cA
    recn
    negidd
    3eqtrd
    @1
    @4
    cpnf
    cmnf
    cxad
    co
    cc0
    @1
    cA
    cpnf
    @3
    cmnf
    cxad
    @1
    id
    @1
    @3
    cpnf
    cxne
    cmnf
    cA
    cpnf
    xnegeq
    xnegpnf
    syl6eq
    oveq12d
    pnfaddmnf
    syl6eq
    @2
    @4
    cmnf
    cpnf
    cxad
    co
    cc0
    @2
    cA
    cmnf
    @3
    cpnf
    cxad
    @2
    id
    @2
    @3
    cmnf
    cxne
    cpnf
    cA
    cmnf
    xnegeq
    xnegmnf
    syl6eq
    oveq12d
    mnfaddpnf
    syl6eq
    3jaoi
    sylbi
end
