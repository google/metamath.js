include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cpr.mm"
include "cmul.mm"
include "cphi.mm"
include "cfv.mm"
include "cn.mm"
include "cgcd.mm"
include "eldifi.mm"
include "3ad2ant2.mm"
include "prmnn.mm"
include "syl.mm"
include "simp1.mm"
include "prmz.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "simp3.mm"
include "wb.mm"
include "coprm.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "eulerth.mm"
include "syl3anc.mm"
include "cn0.mm"
include "phiprm.mm"
include "nnm1nn0.mm"
include "eqeltrd.mm"
include "zexpcl.mm"
include "1zzd.mm"
include "moddvds.mm"
include "nn0cnd.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan1d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "zcnd.mm"
include "2nn0.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "expmuld.mm"
include "oveq1d.mm"
include "sq1.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subsq.mm"
include "sylancl.mm"
include "breqtrd.mm"
include "peano2zd.mm"
include "peano2zm.mm"
include "euclemma.mm"
include "dvdsval3.mm"
include "2z.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "clt.mm"
include "2re.mm"
include "nnrpd.mm"
include "0le2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzle.mm"
include "eldifsni.mm"
include "nnred.mm"
include "ltlend.mm"
include "mpbir2and.mm"
include "modid.mm"
include "syl22anc.mm"
include "eqeq2d.mm"
include "df-2.mm"
include "pnpcan2d.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "3bitr3rd.mm"
include "orbi12d.mm"
include "ovex.mm"
include "elpr.mm"
include "sylibr.mm"

theorem lgslem1
  let cA: class A
  let cP: class P


  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) /\ -. P || A ) -> ( ( ( A ^ ( ( P - 1 ) / 2 ) ) + 1 ) mod P ) e. { 0 , 2 } )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
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
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
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
    @9
    c2
    wceq
    #
    wo
    #
    @9
    cc0
    c2
    cpr
    wcel
    @4
    cP
    @8
    cdvds
    wbr
    #
    cP
    @7
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    #
    @12
    @4
    cP
    @8
    @14
    cmul
    co
    #
    cdvds
    wbr
    #
    @16
    @4
    cP
    cA
    cP
    cphi
    cfv
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    @17
    cdvds
    @4
    @20
    cP
    cmo
    co
    c1
    cP
    cmo
    co
    wceq
    #
    cP
    @21
    cdvds
    wbr
    #
    @4
    cP
    cn
    wcel
    #
    @0
    cA
    cP
    cgcd
    co
    #
    c1
    wceq
    @22
    @4
    cP
    cprime
    wcel
    #
    @24
    @2
    @0
    @26
    @3
    cP
    cprime
    @1
    eldifi
    3ad2ant2
    #
    cP
    prmnn
    syl
    #
    @0
    @2
    @3
    simp1
    #
    @4
    @25
    cP
    cA
    cgcd
    co
    #
    c1
    @4
    @0
    cP
    cz
    wcel
    #
    @25
    @30
    wceq
    @29
    @4
    @26
    @31
    @27
    cP
    prmz
    syl
    cA
    cP
    gcdcom
    syl2anc
    @4
    @3
    @30
    c1
    wceq
    #
    @0
    @2
    @3
    simp3
    @4
    @26
    @0
    @3
    @32
    wb
    @27
    @29
    cP
    cA
    coprm
    syl2anc
    mpbid
    eqtrd
    cA
    cP
    eulerth
    syl3anc
    @4
    @24
    @20
    cz
    wcel
    #
    c1
    cz
    wcel
    @22
    @23
    wb
    @28
    @4
    @0
    @19
    cn0
    wcel
    @33
    @29
    @4
    @19
    @5
    cn0
    @4
    @26
    @19
    @5
    wceq
    @27
    cP
    phiprm
    syl
    #
    @4
    @24
    @5
    cn0
    wcel
    @28
    cP
    nnm1nn0
    syl
    #
    eqeltrd
    cA
    @19
    zexpcl
    syl2anc
    @4
    1zzd
    @20
    c1
    cP
    moddvds
    syl3anc
    mpbid
    @4
    @21
    @7
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    cmin
    co
    #
    @17
    @4
    @21
    @36
    c1
    cmin
    co
    @38
    @4
    @20
    @36
    c1
    cmin
    @4
    @20
    cA
    @6
    c2
    cmul
    co
    #
    cexp
    co
    @36
    @4
    @19
    @39
    cA
    cexp
    @4
    @19
    @5
    @39
    @34
    @4
    @5
    c2
    @4
    @5
    @35
    nn0cnd
    @4
    2cnd
    c2
    cc0
    wne
    @4
    2ne0
    a1i
    divcan1d
    eqtr4d
    oveq2d
    @4
    cA
    @6
    c2
    @4
    cA
    @29
    zcnd
    c2
    cn0
    wcel
    @4
    2nn0
    a1i
    @4
    @6
    @2
    @0
    @6
    cn
    wcel
    @3
    cP
    oddprm
    3ad2ant2
    nnnn0d
    #
    expmuld
    eqtrd
    oveq1d
    @37
    c1
    @36
    cmin
    sq1
    oveq2i
    syl6eqr
    @4
    @7
    cc
    wcel
    c1
    cc
    wcel
    #
    @38
    @17
    wceq
    @4
    @7
    @4
    @0
    @6
    cn0
    wcel
    @7
    cz
    wcel
    #
    @29
    @40
    cA
    @6
    zexpcl
    syl2anc
    #
    zcnd
    #
    ax-1cn
    @7
    c1
    subsq
    sylancl
    eqtrd
    breqtrd
    @4
    @26
    @8
    cz
    wcel
    #
    @14
    cz
    wcel
    #
    @18
    @16
    wb
    @27
    @4
    @7
    @43
    peano2zd
    #
    @4
    @42
    @46
    @43
    @7
    peano2zm
    syl
    cP
    @8
    @14
    euclemma
    syl3anc
    mpbid
    @4
    @13
    @10
    @15
    @11
    @4
    @24
    @45
    @13
    @10
    wb
    @28
    @47
    cP
    @8
    dvdsval3
    syl2anc
    @4
    @9
    c2
    cP
    cmo
    co
    #
    wceq
    #
    cP
    @8
    c2
    cmin
    co
    #
    cdvds
    wbr
    #
    @11
    @15
    @4
    @24
    @45
    c2
    cz
    wcel
    #
    @49
    @51
    wb
    @28
    @47
    @52
    @4
    2z
    a1i
    @8
    c2
    cP
    moddvds
    syl3anc
    @4
    @48
    c2
    @9
    @4
    c2
    cr
    wcel
    #
    cP
    crp
    wcel
    cc0
    c2
    cle
    wbr
    #
    c2
    cP
    clt
    wbr
    #
    @48
    c2
    wceq
    @53
    @4
    2re
    a1i
    #
    @4
    cP
    @28
    nnrpd
    @54
    @4
    0le2
    a1i
    @4
    @55
    c2
    cP
    cle
    wbr
    #
    cP
    c2
    wne
    #
    @4
    cP
    c2
    cuz
    cfv
    wcel
    #
    @57
    @4
    @26
    @59
    @27
    cP
    prmuz2
    syl
    c2
    cP
    eluzle
    syl
    @2
    @0
    @58
    @3
    cP
    cprime
    c2
    eldifsni
    3ad2ant2
    @4
    c2
    cP
    @56
    @4
    cP
    @28
    nnred
    ltlend
    mpbir2and
    c2
    cP
    modid
    syl22anc
    eqeq2d
    @4
    @50
    @14
    cP
    cdvds
    @4
    @50
    @8
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @14
    c2
    @60
    @8
    cmin
    df-2
    oveq2i
    @4
    @7
    c1
    c1
    @44
    @41
    @4
    ax-1cn
    a1i
    #
    @61
    pnpcan2d
    syl5eq
    breq2d
    3bitr3rd
    orbi12d
    mpbid
    @9
    cc0
    c2
    @8
    cP
    cmo
    ovex
    elpr
    sylibr
end
