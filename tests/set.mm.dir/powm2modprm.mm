include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "wceq.mm"
include "cmul.mm"
include "wn.mm"
include "simpll.mm"
include "simpr.mm"
include "adantr.mm"
include "m1dvdsndvds.mm"
include "imp.mm"
include "w3a.mm"
include "cfz.mm"
include "eqid.mm"
include "modprminv.mm"
include "eqcomd.mm"
include "syl.mm"
include "syl3anc.mm"
include "modprm1div.mm"
include "biimpar.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "ad2antlr.mm"
include "cn0.mm"
include "prmm2nn0.mm"
include "anim2i.mm"
include "ancoms.mm"
include "zexpcl.mm"
include "cn.mm"
include "prmnn.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "nnrpd.mm"
include "modmulmod.mm"
include "nn0cnd.mm"
include "mulid2d.mm"
include "reexpcl.mm"
include "syl2anr.mm"
include "jca.mm"
include "modabs2.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "eqtr2d.mm"
include "ex.mm"

theorem powm2modprm
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ ) -> ( P || ( A - 1 ) -> ( ( A ^ ( P - 2 ) ) mod P ) = 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    #
    cP
    cA
    c1
    cmin
    co
    cdvds
    wbr
    #
    cA
    cP
    c2
    cmin
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    wceq
    @2
    @3
    wa
    #
    c1
    cA
    @6
    cmul
    co
    cP
    cmo
    co
    #
    @6
    @7
    @0
    @1
    cP
    cA
    cdvds
    wbr
    wn
    #
    c1
    @8
    wceq
    #
    @0
    @1
    @3
    simpll
    @2
    @1
    @3
    @0
    @1
    simpr
    adantr
    @2
    @3
    @9
    cA
    cP
    m1dvdsndvds
    imp
    @0
    @1
    @9
    w3a
    @6
    c1
    cP
    c1
    cmin
    co
    cfz
    co
    wcel
    #
    @8
    c1
    wceq
    #
    wa
    #
    @10
    cA
    cP
    @6
    @6
    eqid
    modprminv
    @13
    @8
    c1
    @11
    @12
    simpr
    eqcomd
    syl
    syl3anc
    @7
    cA
    cP
    cmo
    co
    #
    @6
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    @6
    cmul
    co
    #
    cP
    cmo
    co
    #
    @8
    @6
    @7
    @15
    @17
    cP
    cmo
    @7
    @14
    c1
    @6
    cmul
    @2
    @14
    c1
    wceq
    @3
    cA
    cP
    modprm1div
    biimpar
    oveq1d
    oveq1d
    @7
    cA
    cr
    wcel
    #
    @6
    cz
    wcel
    cP
    crp
    wcel
    #
    @16
    @8
    wceq
    @1
    @19
    @0
    @3
    cA
    zre
    #
    ad2antlr
    @7
    @6
    @7
    @5
    cP
    @7
    @1
    @4
    cn0
    wcel
    #
    wa
    #
    @5
    cz
    wcel
    #
    @2
    @23
    @3
    @1
    @0
    @23
    @0
    @22
    @1
    cP
    prmm2nn0
    #
    anim2i
    ancoms
    #
    adantr
    cA
    @4
    zexpcl
    #
    syl
    @2
    cP
    cn
    wcel
    #
    @3
    @0
    @28
    @1
    cP
    prmnn
    #
    adantr
    #
    adantr
    zmodcld
    nn0zd
    @2
    @20
    @3
    @0
    @20
    @1
    @0
    cP
    @29
    nnrpd
    adantr
    #
    adantr
    cA
    @6
    cP
    modmulmod
    syl3anc
    @7
    @18
    @6
    cP
    cmo
    co
    #
    @6
    @2
    @18
    @32
    wceq
    @3
    @2
    @17
    @6
    cP
    cmo
    @2
    @6
    @2
    @6
    @2
    @5
    cP
    @2
    @23
    @24
    @26
    @27
    syl
    @30
    zmodcld
    nn0cnd
    mulid2d
    oveq1d
    adantr
    @7
    @5
    cr
    wcel
    #
    @20
    wa
    #
    @32
    @6
    wceq
    @2
    @34
    @3
    @2
    @33
    @20
    @1
    @19
    @22
    @33
    @0
    @21
    @25
    cA
    @4
    reexpcl
    syl2anr
    @31
    jca
    adantr
    @5
    cP
    modabs2
    syl
    eqtrd
    3eqtr3d
    eqtr2d
    ex
end
