include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "wceq.mm"
include "wi.mm"
include "cn.mm"
include "prmnn.mm"
include "dvdsmodexp.mm"
include "3exp.mm"
include "sylc.mm"
include "adantr.mm"
include "wn.mm"
include "cgcd.mm"
include "c1.mm"
include "coprm.mm"
include "prmz.mm"
include "gcdcom.mm"
include "sylan.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "w3a.mm"
include "cphi.mm"
include "cfv.mm"
include "cmul.mm"
include "cr.mm"
include "crp.mm"
include "cn0.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "phicld.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "zred.mm"
include "1red.mm"
include "nnrpd.mm"
include "eulerth.mm"
include "syl3an1.mm"
include "modmul1.mm"
include "syl221anc.mm"
include "cmin.mm"
include "phiprm.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcnd.mm"
include "expm1t.mm"
include "eqtr4d.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "3expia.mm"
include "sylbid.mm"
include "pm2.61d.mm"

theorem fermltl
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ ) -> ( ( A ^ P ) mod P ) = ( A mod P ) )

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
    cdvds
    wbr
    #
    cA
    cP
    cexp
    co
    #
    cP
    cmo
    co
    #
    cA
    cP
    cmo
    co
    #
    wceq
    #
    @0
    @3
    @7
    wi
    #
    @1
    @0
    cP
    cn
    wcel
    #
    @9
    @8
    cP
    prmnn
    #
    @10
    @9
    @9
    @3
    @7
    cA
    cP
    cP
    dvdsmodexp
    3exp
    sylc
    adantr
    @2
    @3
    wn
    #
    cA
    cP
    cgcd
    co
    #
    c1
    wceq
    #
    @7
    @2
    @11
    cP
    cA
    cgcd
    co
    #
    c1
    wceq
    @13
    cP
    cA
    coprm
    @2
    @14
    @12
    c1
    @0
    cP
    cz
    wcel
    @1
    @14
    @12
    wceq
    cP
    prmz
    cP
    cA
    gcdcom
    sylan
    eqeq1d
    bitrd
    @0
    @1
    @13
    @7
    @0
    @1
    @13
    w3a
    #
    cA
    cP
    cphi
    cfv
    #
    cexp
    co
    #
    cA
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    cA
    cmul
    co
    #
    cP
    cmo
    co
    #
    @5
    @6
    @15
    @17
    cr
    wcel
    c1
    cr
    wcel
    @1
    cP
    crp
    wcel
    @17
    cP
    cmo
    co
    c1
    cP
    cmo
    co
    wceq
    #
    @19
    @21
    wceq
    @15
    @17
    @15
    @1
    @16
    cn0
    wcel
    @17
    cz
    wcel
    @0
    @1
    @13
    simp2
    #
    @15
    @16
    @15
    cP
    @0
    @1
    @9
    @13
    @10
    3ad2ant1
    #
    phicld
    nnnn0d
    cA
    @16
    zexpcl
    syl2anc
    zred
    @15
    1red
    @23
    @15
    cP
    @24
    nnrpd
    @0
    @9
    @1
    @13
    @22
    @10
    cA
    cP
    eulerth
    syl3an1
    @17
    c1
    cA
    cP
    modmul1
    syl221anc
    @15
    @18
    @4
    cP
    cmo
    @15
    @18
    cA
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    cA
    cmul
    co
    #
    @4
    @15
    @17
    @26
    cA
    cmul
    @15
    @16
    @25
    cA
    cexp
    @0
    @1
    @16
    @25
    wceq
    @13
    cP
    phiprm
    3ad2ant1
    oveq2d
    oveq1d
    @15
    cA
    cc
    wcel
    @9
    @4
    @27
    wceq
    @15
    cA
    @23
    zcnd
    #
    @24
    cA
    cP
    expm1t
    syl2anc
    eqtr4d
    oveq1d
    @15
    @20
    cA
    cP
    cmo
    @15
    cA
    @28
    mulid2d
    oveq1d
    3eqtr3d
    3expia
    sylbid
    pm2.61d
end
