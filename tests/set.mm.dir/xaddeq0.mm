include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cxne.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "wi.mm"
include "elxr.mm"
include "simpll.mm"
include "rexrd.mm"
include "xnegneg.mm"
include "syl.mm"
include "xnegcld.mm"
include "xaddid2.mm"
include "simplr.mm"
include "xaddcom.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "simpr.mm"
include "xpncan.mm"
include "ancoms.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "xnegeq.mm"
include "ex.mm"
include "wne.mm"
include "wn.mm"
include "0re.mm"
include "renepnf.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "xaddpnf2.mm"
include "stoic1a.mm"
include "nne.mm"
include "sylib.mm"
include "xnegmnf.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "renemnf.mm"
include "xaddmnf2.mm"
include "xnegpnf.mm"
include "3jaoian.mm"
include "sylanb.mm"
include "xnegcl.mm"
include "ad2antlr.mm"
include "xnegid.mm"
include "3eqtrd.mm"
include "impbid.mm"

theorem xaddeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( ( A +e B ) = 0 <-> A = -e B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cxad
    co
    #
    cc0
    wceq
    #
    cA
    cB
    cxne
    #
    wceq
    #
    @0
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
    @1
    @4
    @6
    wi
    #
    cA
    elxr
    @7
    @1
    @10
    @8
    @9
    @7
    @1
    wa
    #
    @4
    @6
    @11
    @4
    wa
    #
    cA
    cxne
    #
    cxne
    #
    cA
    @5
    @12
    @0
    @14
    cA
    wceq
    @12
    cA
    @7
    @1
    @4
    simpll
    rexrd
    #
    cA
    xnegneg
    syl
    @12
    @13
    cB
    wceq
    @14
    @5
    wceq
    @12
    cc0
    @13
    cxad
    co
    #
    @13
    cB
    @12
    @13
    cxr
    wcel
    @16
    @13
    wceq
    @12
    cA
    @15
    xnegcld
    @13
    xaddid2
    syl
    @12
    @3
    @13
    cxad
    co
    cB
    cA
    cxad
    co
    #
    @13
    cxad
    co
    #
    @16
    cB
    @12
    @3
    @17
    @13
    cxad
    @12
    @0
    @1
    @3
    @17
    wceq
    @15
    @7
    @1
    @4
    simplr
    cA
    cB
    xaddcom
    syl2anc
    oveq1d
    @12
    @3
    cc0
    @13
    cxad
    @11
    @4
    simpr
    oveq1d
    @11
    @18
    cB
    wceq
    #
    @4
    @1
    @7
    @19
    cB
    cA
    xpncan
    ancoms
    adantr
    3eqtr3d
    eqtr3d
    @13
    cB
    xnegeq
    syl
    eqtr3d
    ex
    @8
    @1
    wa
    #
    @4
    @6
    @20
    @4
    wa
    #
    cA
    cpnf
    @5
    @8
    @1
    @4
    simpll
    #
    @21
    @5
    cmnf
    cxne
    #
    cpnf
    @21
    cB
    cmnf
    wceq
    #
    @5
    @23
    wceq
    @21
    cB
    cmnf
    wne
    #
    wn
    #
    @24
    @21
    @1
    cpnf
    cB
    cxad
    co
    #
    cpnf
    wceq
    #
    wn
    @26
    @8
    @1
    @4
    simplr
    @21
    @27
    cpnf
    @21
    @27
    cc0
    cpnf
    @21
    @3
    @27
    cc0
    @21
    cA
    cpnf
    cB
    cxad
    @22
    oveq1d
    @20
    @4
    simpr
    eqtr3d
    cc0
    cr
    wcel
    #
    cc0
    cpnf
    wne
    @21
    0re
    cc0
    renepnf
    mp1i
    eqnetrd
    neneqd
    @1
    @25
    @28
    cB
    xaddpnf2
    stoic1a
    syl2anc
    cB
    cmnf
    nne
    sylib
    cB
    cmnf
    xnegeq
    syl
    xnegmnf
    syl6req
    eqtrd
    ex
    @9
    @1
    wa
    #
    @4
    @6
    @30
    @4
    wa
    #
    cA
    cmnf
    @5
    @9
    @1
    @4
    simpll
    #
    @31
    @5
    cpnf
    cxne
    #
    cmnf
    @31
    cB
    cpnf
    wceq
    #
    @5
    @33
    wceq
    @31
    cB
    cpnf
    wne
    #
    wn
    #
    @34
    @31
    @1
    cmnf
    cB
    cxad
    co
    #
    cmnf
    wceq
    #
    wn
    @36
    @9
    @1
    @4
    simplr
    @31
    @37
    cmnf
    @31
    @37
    cc0
    cmnf
    @31
    @3
    @37
    cc0
    @31
    cA
    cmnf
    cB
    cxad
    @32
    oveq1d
    @30
    @4
    simpr
    eqtr3d
    @29
    cc0
    cmnf
    wne
    @31
    0re
    cc0
    renemnf
    mp1i
    eqnetrd
    neneqd
    @1
    @35
    @38
    cB
    xaddmnf2
    stoic1a
    syl2anc
    cB
    cpnf
    nne
    sylib
    cB
    cpnf
    xnegeq
    syl
    xnegpnf
    syl6req
    eqtrd
    ex
    3jaoian
    sylanb
    @2
    @6
    @4
    @2
    @6
    wa
    #
    @3
    @5
    cB
    cxad
    co
    #
    cB
    @5
    cxad
    co
    #
    cc0
    @39
    cA
    @5
    cB
    cxad
    @2
    @6
    simpr
    oveq1d
    @39
    @5
    cxr
    wcel
    #
    @1
    @40
    @41
    wceq
    @1
    @42
    @0
    @6
    cB
    xnegcl
    ad2antlr
    @0
    @1
    @6
    simplr
    @5
    cB
    xaddcom
    syl2anc
    @1
    @41
    cc0
    wceq
    @0
    @6
    cB
    xnegid
    ad2antlr
    3eqtrd
    ex
    impbid
end
