include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "cc0.mm"
include "csp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cno.mm"
include "wa.mm"
include "cr.mm"
include "hiidrcl.mm"
include "adantr.mm"
include "ax-his4.mm"
include "sqrtgt0.mm"
include "syl2anc.mm"
include "ex.mm"
include "wceq.mm"
include "wn.mm"
include "oveq1.mm"
include "hi01.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "sqrt0.mm"
include "syl6eq.mm"
include "wb.mm"
include "hiidge0.mm"
include "resqrtcld.mm"
include "0re.mm"
include "lttri3.mm"
include "sylancl.mm"
include "simpr.mm"
include "syl6bi.mm"
include "syld.mm"
include "necon2ad.mm"
include "impbid.mm"
include "normval.mm"
include "breq2d.mm"
include "bitr4d.mm"

theorem normgt0
  let cA: class A


  assert |- ( A e. ~H -> ( A =/= 0h <-> 0 < ( normh ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    cc0
    cA
    cA
    csp
    co
    #
    csqrt
    cfv
    #
    clt
    wbr
    #
    cc0
    cA
    cno
    cfv
    #
    clt
    wbr
    @0
    @1
    @4
    @0
    @1
    @4
    @0
    @1
    wa
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    @4
    @0
    @6
    @1
    cA
    hiidrcl
    #
    adantr
    cA
    ax-his4
    @2
    sqrtgt0
    syl2anc
    ex
    @0
    @4
    cA
    c0v
    @0
    cA
    c0v
    wceq
    #
    @3
    cc0
    wceq
    #
    @4
    wn
    #
    @0
    @8
    @9
    @0
    @8
    wa
    #
    @3
    cc0
    csqrt
    cfv
    cc0
    @11
    @2
    cc0
    csqrt
    @8
    @0
    @2
    c0v
    cA
    csp
    co
    cc0
    cA
    c0v
    cA
    csp
    oveq1
    cA
    hi01
    sylan9eqr
    fveq2d
    sqrt0
    syl6eq
    ex
    @0
    @9
    @3
    cc0
    clt
    wbr
    wn
    #
    @10
    wa
    #
    @10
    @0
    @3
    cr
    wcel
    cc0
    cr
    wcel
    @9
    @13
    wb
    @0
    @2
    @7
    cA
    hiidge0
    resqrtcld
    0re
    @3
    cc0
    lttri3
    sylancl
    @12
    @10
    simpr
    syl6bi
    syld
    necon2ad
    impbid
    @0
    @5
    @3
    cc0
    clt
    cA
    normval
    breq2d
    bitr4d
end
