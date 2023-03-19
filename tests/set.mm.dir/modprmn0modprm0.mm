include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cfzo.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "c1.mm"
include "simpl1.mm"
include "cn.mm"
include "prmnn.mm"
include "zmodfzo.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3adant3.mm"
include "wi.mm"
include "fzo1fzo0n0.mm"
include "simplbi2com.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "adantr.mm"
include "simpr.mm"
include "nnnn0modprm0.mm"
include "syl3anc.mm"
include "cc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "cn0.mm"
include "anim1i.mm"
include "ancomd.mm"
include "zmodcl.mm"
include "nn0cn.mm"
include "3syl.mm"
include "mulcom.mm"
include "syl2anr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "adantl.mm"
include "zre.mm"
include "3ad2ant2.mm"
include "nnrpd.mm"
include "3ad2ant1.mm"
include "modaddmulmod.mm"
include "syl31anc.mm"
include "zcn.mm"
include "mulcomd.mm"
include "ex.mm"
include "imp.mm"
include "3eqtrrd.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem modprmn0modprm0
  let cP: class P
  let vj: setvar j
  let cI: class I
  let cN: class N

  disjoint I j
  disjoint N j
  disjoint P j
  assert |- ( ( P e. Prime /\ N e. ZZ /\ ( N mod P ) =/= 0 ) -> ( I e. ( 0 ..^ P ) -> E. j e. ( 0 ..^ P ) ( ( I + ( j x. N ) ) mod P ) = 0 ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cP
    cmo
    co
    #
    cc0
    wne
    #
    w3a
    #
    cI
    cc0
    cP
    cfzo
    co
    #
    wcel
    #
    cI
    vj
    cv
    #
    cN
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    cc0
    wceq
    #
    vj
    @5
    wrex
    #
    @4
    @6
    wa
    #
    @12
    cI
    @7
    @2
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    cc0
    wceq
    #
    vj
    @5
    wrex
    #
    @13
    @0
    @2
    c1
    cP
    cfzo
    co
    wcel
    #
    @6
    @18
    @0
    @1
    @3
    @6
    simpl1
    @4
    @19
    @6
    @4
    @2
    @5
    wcel
    #
    @19
    @0
    @1
    @20
    @3
    @1
    @0
    @20
    @0
    @1
    cP
    cn
    wcel
    #
    @20
    cP
    prmnn
    #
    cN
    cP
    zmodfzo
    sylan2
    ancoms
    3adant3
    @3
    @0
    @20
    @19
    wi
    @1
    @19
    @20
    @3
    @2
    cP
    fzo1fzo0n0
    simplbi2com
    3ad2ant3
    mpd
    adantr
    @4
    @6
    simpr
    cP
    vj
    cI
    @2
    nnnn0modprm0
    syl3anc
    @13
    @11
    @17
    vj
    @5
    @13
    @7
    @5
    wcel
    #
    wa
    #
    @10
    @16
    cc0
    @24
    @16
    cI
    @2
    @7
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    cI
    cN
    @7
    cmul
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    @10
    @24
    @15
    @26
    cP
    cmo
    @24
    @14
    @25
    cI
    caddc
    @23
    @7
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @14
    @25
    wceq
    @13
    @23
    @7
    @7
    cc0
    cP
    elfzoelz
    #
    zcnd
    #
    @4
    @32
    @6
    @0
    @1
    @32
    @3
    @0
    @1
    wa
    #
    @1
    @21
    wa
    @2
    cn0
    wcel
    @32
    @35
    @21
    @1
    @0
    @21
    @1
    @22
    anim1i
    ancomd
    cN
    cP
    zmodcl
    @2
    nn0cn
    3syl
    3adant3
    adantr
    @7
    @2
    mulcom
    syl2anr
    oveq2d
    oveq1d
    @24
    cI
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @7
    cz
    wcel
    #
    cP
    crp
    wcel
    #
    @27
    @30
    wceq
    @13
    @36
    @23
    @6
    @36
    @4
    @6
    cI
    cI
    cc0
    cP
    elfzoelz
    zred
    adantl
    adantr
    @13
    @37
    @23
    @4
    @37
    @6
    @1
    @0
    @37
    @3
    cN
    zre
    3ad2ant2
    adantr
    adantr
    @23
    @38
    @13
    @33
    adantl
    @13
    @39
    @23
    @4
    @39
    @6
    @0
    @1
    @39
    @3
    @0
    cP
    @22
    nnrpd
    3ad2ant1
    adantr
    adantr
    cI
    cN
    @7
    cP
    modaddmulmod
    syl31anc
    @24
    @29
    @9
    cP
    cmo
    @24
    @28
    @8
    cI
    caddc
    @13
    @23
    @28
    @8
    wceq
    #
    @4
    @23
    @40
    wi
    #
    @6
    @1
    @0
    @41
    @3
    @1
    @23
    @40
    @1
    @23
    wa
    cN
    @7
    @1
    cN
    cc
    wcel
    @23
    cN
    zcn
    adantr
    @23
    @31
    @1
    @34
    adantl
    mulcomd
    ex
    3ad2ant2
    adantr
    imp
    oveq2d
    oveq1d
    3eqtrrd
    eqeq1d
    rexbidva
    mpbird
    ex
end
