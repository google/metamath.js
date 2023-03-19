include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "ck.mm"
include "co.mm"
include "csn.mm"
include "cspn.mm"
include "cpjh.mm"
include "cv.mm"
include "wral.mm"
include "csp.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "csm.mm"
include "oveq1.mm"
include "sq1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cc.mm"
include "hicl.mm"
include "ancoms.mm"
include "div1d.mm"
include "sylan9eqr.mm"
include "an32s.mm"
include "oveq1d.mm"
include "c0v.mm"
include "wne.mm"
include "simpll.mm"
include "simpr.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "normne0.mm"
include "syl5ib.mm"
include "imp.mm"
include "adantr.mm"
include "pjspansn.mm"
include "syl3anc.mm"
include "kbval.mm"
include "3anidm12.mm"
include "adantlr.mm"
include "3eqtr4rd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "wfn.mm"
include "wf.mm"
include "kbop.mm"
include "anidms.mm"
include "ffn.mm"
include "syl.mm"
include "cch.mm"
include "spansnch.mm"
include "pjfn.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem kbpj
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ ( normh ` A ) = 1 ) -> ( A ketbra A ) = ( projh ` ( span ` { A } ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cno
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cA
    cA
    ck
    co
    #
    cA
    csn
    cspn
    cfv
    #
    cpjh
    cfv
    #
    wceq
    #
    vx
    cv
    #
    @4
    cfv
    #
    @8
    @6
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    @3
    @11
    vx
    chil
    @3
    @8
    chil
    wcel
    #
    wa
    #
    @8
    cA
    csp
    co
    #
    @1
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cA
    csm
    co
    #
    @15
    cA
    csm
    co
    #
    @10
    @9
    @14
    @17
    @15
    cA
    csm
    @0
    @13
    @2
    @17
    @15
    wceq
    @2
    @0
    @13
    wa
    #
    @17
    @15
    c1
    cdiv
    co
    @15
    @2
    @16
    c1
    @15
    cdiv
    @2
    @16
    c1
    c2
    cexp
    co
    c1
    @1
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    oveq2d
    @20
    @15
    @13
    @0
    @15
    cc
    wcel
    @8
    cA
    hicl
    ancoms
    div1d
    sylan9eqr
    an32s
    oveq1d
    @14
    @0
    @13
    cA
    c0v
    wne
    #
    @10
    @18
    wceq
    @0
    @2
    @13
    simpll
    @3
    @13
    simpr
    @3
    @21
    @13
    @0
    @2
    @21
    @2
    @1
    cc0
    wne
    #
    @0
    @21
    @2
    @22
    c1
    cc0
    wne
    ax-1ne0
    @1
    c1
    cc0
    neeq1
    mpbiri
    cA
    normne0
    syl5ib
    imp
    adantr
    cA
    @8
    pjspansn
    syl3anc
    @0
    @13
    @9
    @19
    wceq
    #
    @2
    @0
    @13
    @23
    cA
    cA
    @8
    kbval
    3anidm12
    adantlr
    3eqtr4rd
    ralrimiva
    @0
    @7
    @12
    wb
    #
    @2
    @0
    @4
    chil
    wfn
    #
    @6
    chil
    wfn
    #
    @24
    @0
    chil
    chil
    @4
    wf
    #
    @25
    @0
    @27
    cA
    cA
    kbop
    anidms
    chil
    chil
    @4
    ffn
    syl
    @0
    @5
    cch
    wcel
    @26
    cA
    spansnch
    @5
    pjfn
    syl
    vx
    chil
    @4
    @6
    eqfnfv
    syl2anc
    adantr
    mpbird
end
