include "cr.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cm1r.mm"
include "cmr.mm"
include "co.mm"
include "c0r.mm"
include "cop.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "cnr.mm"
include "elreal2.mm"
include "simplbi.mm"
include "m1r.mm"
include "mulclsr.mm"
include "sylancl.mm"
include "opelreal.mm"
include "sylibr.mm"
include "cplr.mm"
include "simprbi.mm"
include "oveq1d.mm"
include "addresr.mm"
include "syl2anc.mm"
include "pn0sr.mm"
include "opeq1d.mm"
include "df-0.mm"
include "syl6eqr.mm"
include "syl.mm"
include "3eqtrd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"

theorem axrnegex
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. RR -> E. x e. RR ( A + x ) = 0 )

  proof
    cA
    cr
    wcel
    #
    cA
    c1st
    cfv
    #
    cm1r
    cmr
    co
    #
    c0r
    cop
    #
    cr
    wcel
    #
    cA
    @3
    caddc
    co
    #
    cc0
    wceq
    #
    cA
    vx
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vx
    cr
    wrex
    @0
    @2
    cnr
    wcel
    #
    @4
    @0
    @1
    cnr
    wcel
    #
    cm1r
    cnr
    wcel
    @10
    @0
    @11
    cA
    @1
    c0r
    cop
    #
    wceq
    #
    cA
    elreal2
    #
    simplbi
    #
    m1r
    @1
    cm1r
    mulclsr
    sylancl
    #
    @2
    opelreal
    sylibr
    @0
    @5
    @12
    @3
    caddc
    co
    #
    @1
    @2
    cplr
    co
    #
    c0r
    cop
    #
    cc0
    @0
    cA
    @12
    @3
    caddc
    @0
    @11
    @13
    @14
    simprbi
    oveq1d
    @0
    @11
    @10
    @17
    @19
    wceq
    @15
    @16
    @1
    @2
    addresr
    syl2anc
    @0
    @11
    @19
    cc0
    wceq
    @15
    @11
    @19
    c0r
    c0r
    cop
    cc0
    @11
    @18
    c0r
    c0r
    @1
    pn0sr
    opeq1d
    df-0
    syl6eqr
    syl
    3eqtrd
    @9
    @6
    vx
    @3
    cr
    @7
    @3
    wceq
    @8
    @5
    cc0
    @7
    @3
    cA
    caddc
    oveq2
    eqeq1d
    rspcev
    syl2anc
end
