include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "w3a.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cpjh.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "csp.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "csm.mm"
include "cort.mm"
include "cch.mm"
include "wrex.mm"
include "spansnch.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wa.mm"
include "eqid.mm"
include "pjeq.mm"
include "mpbii.mm"
include "simprd.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "ad2antll.mm"
include "caddc.mm"
include "cc0.mm"
include "pjhcl.mm"
include "adantr.mm"
include "choccl.mm"
include "syl.mm"
include "chel.mm"
include "sylan.mm"
include "simpl1.mm"
include "ax-his2.mm"
include "syl3anc.mm"
include "csh.mm"
include "spansnsh.mm"
include "spansnid.mm"
include "simpr.mm"
include "shocorth.mm"
include "3impib.mm"
include "wb.mm"
include "orthcom.mm"
include "syldan.mm"
include "mpbid.mm"
include "3ad2antl1.mm"
include "oveq2d.mm"
include "cc.mm"
include "hicl.mm"
include "addid1d.mm"
include "3eqtrd.mm"
include "adantrr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simpl3.mm"
include "axpjcl.mm"
include "normcan.mm"
include "eqtr2d.mm"
include "rexlimddv.mm"

theorem pjspansn
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( ( A e. ~H /\ B e. ~H /\ A =/= 0h ) -> ( ( projh ` ( span ` { A } ) ) ` B ) = ( ( ( B .ih A ) / ( ( normh ` A ) ^ 2 ) ) .h A ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    w3a
    #
    cB
    cB
    cA
    csn
    cspn
    cfv
    #
    cpjh
    cfv
    cfv
    #
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    @5
    cB
    cA
    csp
    co
    #
    cA
    cno
    cfv
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
    wceq
    vy
    @4
    cort
    cfv
    #
    @3
    @4
    cch
    wcel
    #
    @1
    @8
    vy
    @13
    wrex
    #
    @0
    @1
    @14
    @2
    cA
    spansnch
    #
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @14
    @1
    wa
    #
    @5
    @4
    wcel
    #
    @15
    @19
    @5
    @5
    wceq
    @20
    @15
    wa
    @5
    eqid
    vy
    cB
    @5
    @4
    pjeq
    mpbii
    simprd
    syl2anc
    @3
    @6
    @13
    wcel
    #
    @8
    wa
    #
    wa
    #
    @12
    @5
    cA
    csp
    co
    #
    @10
    cdiv
    co
    #
    cA
    csm
    co
    #
    @5
    @23
    @11
    @25
    cA
    csm
    @23
    @9
    @24
    @10
    cdiv
    @23
    @9
    @7
    cA
    csp
    co
    #
    @24
    @8
    @9
    @27
    wceq
    @3
    @21
    cB
    @7
    cA
    csp
    oveq1
    ad2antll
    @3
    @21
    @27
    @24
    wceq
    @8
    @3
    @21
    wa
    #
    @27
    @24
    @6
    cA
    csp
    co
    #
    caddc
    co
    #
    @24
    cc0
    caddc
    co
    @24
    @28
    @5
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @0
    @27
    @30
    wceq
    @3
    @31
    @21
    @3
    @14
    @1
    @31
    @17
    @18
    cB
    @4
    pjhcl
    syl2anc
    adantr
    #
    @3
    @13
    cch
    wcel
    #
    @21
    @32
    @0
    @1
    @34
    @2
    @0
    @14
    @34
    @16
    @4
    choccl
    syl
    #
    3ad2ant1
    @6
    @13
    chel
    #
    sylan
    @0
    @1
    @2
    @21
    simpl1
    #
    @5
    @6
    cA
    ax-his2
    syl3anc
    @28
    @29
    cc0
    @24
    caddc
    @0
    @1
    @21
    @29
    cc0
    wceq
    #
    @2
    @0
    @21
    wa
    #
    cA
    @6
    csp
    co
    cc0
    wceq
    #
    @38
    @39
    @4
    csh
    wcel
    #
    cA
    @4
    wcel
    #
    @21
    @40
    @0
    @41
    @21
    cA
    spansnsh
    adantr
    @0
    @42
    @21
    cA
    spansnid
    adantr
    @0
    @21
    simpr
    @41
    @42
    @21
    @40
    cA
    @6
    @4
    shocorth
    3impib
    syl3anc
    @0
    @21
    @32
    @40
    @38
    wb
    @0
    @34
    @21
    @32
    @35
    @36
    sylan
    cA
    @6
    orthcom
    syldan
    mpbid
    3ad2antl1
    oveq2d
    @28
    @24
    @28
    @31
    @0
    @24
    cc
    wcel
    @33
    @37
    @5
    cA
    hicl
    syl2anc
    addid1d
    3eqtrd
    adantrr
    eqtrd
    oveq1d
    oveq1d
    @23
    @0
    @2
    @20
    @26
    @5
    wceq
    @0
    @1
    @2
    @22
    simpl1
    @0
    @1
    @2
    @22
    simpl3
    @3
    @20
    @22
    @3
    @14
    @1
    @20
    @17
    @18
    cB
    @4
    axpjcl
    syl2anc
    adantr
    @5
    cA
    normcan
    syl3anc
    eqtr2d
    rexlimddv
end
