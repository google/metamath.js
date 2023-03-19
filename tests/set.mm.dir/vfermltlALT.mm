include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmo.mm"
include "c2.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "2m1e1.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "prmz.mm"
include "zcnd.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "eqtrd.mm"
include "3ad2ant1.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "cn0.mm"
include "prmm2nn0.mm"
include "expp1d.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "wa.mm"
include "anim1i.mm"
include "ancomd.mm"
include "zexpcl.mm"
include "syl.mm"
include "zred.mm"
include "3adant3.mm"
include "simp2.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "modmulmod.mm"
include "syl3anc.mm"
include "zre.mm"
include "adantl.mm"
include "adantr.mm"
include "reexpcld.mm"
include "modcld.mm"
include "recnd.mm"
include "mulcomd.mm"
include "3eqtr2d.mm"
include "cfz.mm"
include "eqid.mm"
include "modprminv.mm"
include "simprd.mm"

theorem vfermltlALT
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ /\ -. P || A ) -> ( ( A ^ ( P - 1 ) ) mod P ) = 1 )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cP
    cA
    cdvds
    wbr
    wn
    #
    w3a
    #
    cA
    cP
    c1
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
    cA
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
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    @3
    @6
    @8
    cA
    cmul
    co
    #
    cP
    cmo
    co
    #
    @9
    cA
    cmul
    co
    #
    cP
    cmo
    co
    #
    @11
    @3
    @5
    @12
    cP
    cmo
    @3
    @5
    cA
    @7
    c1
    caddc
    co
    #
    cexp
    co
    @12
    @3
    @4
    @16
    cA
    cexp
    @0
    @1
    @4
    @16
    wceq
    @2
    @0
    @4
    cP
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @16
    @0
    c1
    @17
    cP
    cmin
    @0
    @17
    c1
    @17
    c1
    wceq
    @0
    2m1e1
    a1i
    eqcomd
    oveq2d
    @0
    cP
    c2
    c1
    @0
    cP
    cP
    prmz
    zcnd
    @0
    2cnd
    @0
    1cnd
    subsubd
    eqtrd
    3ad2ant1
    oveq2d
    @3
    cA
    @7
    @1
    @0
    cA
    cc
    wcel
    #
    @2
    cA
    zcn
    #
    3ad2ant2
    @0
    @1
    @7
    cn0
    wcel
    #
    @2
    cP
    prmm2nn0
    #
    3ad2ant1
    expp1d
    eqtrd
    oveq1d
    @3
    @8
    cr
    wcel
    #
    @1
    cP
    crp
    wcel
    #
    @15
    @13
    wceq
    @0
    @1
    @22
    @2
    @0
    @1
    wa
    #
    @8
    @24
    @1
    @20
    wa
    @8
    cz
    wcel
    @24
    @20
    @1
    @0
    @20
    @1
    @21
    anim1i
    ancomd
    cA
    @7
    zexpcl
    syl
    zred
    3adant3
    @0
    @1
    @2
    simp2
    @0
    @1
    @23
    @2
    @0
    cP
    cP
    prmnn
    nnrpd
    #
    3ad2ant1
    @8
    cA
    cP
    modmulmod
    syl3anc
    @3
    @14
    @10
    cP
    cmo
    @0
    @1
    @14
    @10
    wceq
    @2
    @24
    @9
    cA
    @24
    @9
    @24
    @8
    cP
    @24
    cA
    @7
    @1
    cA
    cr
    wcel
    @0
    cA
    zre
    adantl
    @0
    @20
    @1
    @21
    adantr
    reexpcld
    @0
    @23
    @1
    @25
    adantr
    modcld
    recnd
    @1
    @18
    @0
    @19
    adantl
    mulcomd
    3adant3
    oveq1d
    3eqtr2d
    @3
    @9
    c1
    @4
    cfz
    co
    wcel
    @11
    c1
    wceq
    cA
    cP
    @9
    @9
    eqid
    modprminv
    simprd
    eqtrd
end
