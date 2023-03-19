include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cmul.mm"
include "wa.mm"
include "wceq.mm"
include "cmo.mm"
include "cgcd.mm"
include "simprr.mm"
include "prmdiv.mm"
include "adantr.mm"
include "simprd.mm"
include "wi.mm"
include "simpl1.mm"
include "prmz.mm"
include "syl.mm"
include "simpl2.mm"
include "elfzelz.mm"
include "ad2antrl.mm"
include "zmulcld.mm"
include "1z.mm"
include "zsubcl.mm"
include "sylancl.mm"
include "simpld.mm"
include "dvds2sub.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "zcnd.mm"
include "1cnd.mm"
include "nnncan2d.mm"
include "cn0.mm"
include "elfznn0.mm"
include "nn0red.mm"
include "recnd.mm"
include "subdid.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "simpl3.mm"
include "wb.mm"
include "coprm.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "zsubcld.mm"
include "coprmdvds.mm"
include "cn.mm"
include "prmnn.mm"
include "moddvds.mm"
include "mpbird.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "clt.mm"
include "nnrpd.mm"
include "elfzle1.mm"
include "elfzle2.mm"
include "zltlem1.mm"
include "modid.mm"
include "syl22anc.mm"
include "c2.mm"
include "cexp.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "uznn0sub.mm"
include "3syl.mm"
include "zexpcl.mm"
include "zred.mm"
include "modabs2.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "caddc.mm"
include "1e0p1.mm"
include "wss.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "sseli.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "biimprd.mm"
include "anim12d.mm"
include "syl5com.mm"
include "impbid.mm"

theorem prmdiveq
  let cA: class A
  let cP: class P
  let cR: class R
  let cS: class S
  assume prmdiv.1: |- R = ( ( A ^ ( P - 2 ) ) mod P )


  assert |- ( ( P e. Prime /\ A e. ZZ /\ -. P || A ) -> ( ( S e. ( 0 ... ( P - 1 ) ) /\ P || ( ( A x. S ) - 1 ) ) <-> S = R ) )

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
    cS
    cc0
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    cP
    cA
    cS
    cmul
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    cS
    cR
    wceq
    #
    @3
    @10
    @11
    @3
    @10
    wa
    #
    cS
    cP
    cmo
    co
    #
    cR
    cP
    cmo
    co
    #
    cS
    cR
    @12
    @13
    @14
    wceq
    #
    cP
    cS
    cR
    cmin
    co
    #
    cdvds
    wbr
    #
    @12
    cP
    cA
    @16
    cmul
    co
    #
    cdvds
    wbr
    #
    cP
    cA
    cgcd
    co
    c1
    wceq
    #
    @17
    @12
    cP
    @8
    cA
    cR
    cmul
    co
    #
    c1
    cmin
    co
    #
    cmin
    co
    #
    @18
    cdvds
    @12
    @9
    cP
    @22
    cdvds
    wbr
    #
    cP
    @23
    cdvds
    wbr
    #
    @3
    @6
    @9
    simprr
    @12
    cR
    c1
    @4
    cfz
    co
    #
    wcel
    #
    @24
    @3
    @27
    @24
    wa
    #
    @10
    cA
    cP
    cR
    prmdiv.1
    prmdiv
    #
    adantr
    #
    simprd
    @12
    cP
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @22
    cz
    wcel
    #
    @9
    @24
    wa
    @25
    wi
    @12
    @0
    @31
    @0
    @1
    @2
    @10
    simpl1
    #
    cP
    prmz
    syl
    #
    @12
    @7
    cz
    wcel
    c1
    cz
    wcel
    #
    @32
    @12
    cA
    cS
    @0
    @1
    @2
    @10
    simpl2
    #
    @6
    cS
    cz
    wcel
    #
    @3
    @9
    cS
    cc0
    @4
    elfzelz
    ad2antrl
    #
    zmulcld
    #
    1z
    @7
    c1
    zsubcl
    sylancl
    @12
    @21
    cz
    wcel
    @36
    @33
    @12
    cA
    cR
    @37
    @12
    @27
    cR
    cz
    wcel
    #
    @12
    @27
    @24
    @30
    simpld
    cR
    c1
    @4
    elfzelz
    syl
    #
    zmulcld
    #
    1z
    @21
    c1
    zsubcl
    sylancl
    cP
    @8
    @22
    dvds2sub
    syl3anc
    mp2and
    @12
    @23
    @7
    @21
    cmin
    co
    @18
    @12
    @7
    @21
    c1
    @12
    @7
    @40
    zcnd
    @12
    @21
    @43
    zcnd
    @12
    1cnd
    nnncan2d
    @12
    cA
    cS
    cR
    @12
    cA
    @37
    zcnd
    @12
    cS
    @12
    cS
    @6
    cS
    cn0
    wcel
    @3
    @9
    cS
    @4
    elfznn0
    ad2antrl
    nn0red
    #
    recnd
    @12
    cR
    @42
    zcnd
    subdid
    eqtr4d
    breqtrd
    @12
    @2
    @20
    @0
    @1
    @2
    @10
    simpl3
    @12
    @0
    @1
    @2
    @20
    wb
    @34
    @37
    cP
    cA
    coprm
    syl2anc
    mpbid
    @12
    @31
    @1
    @16
    cz
    wcel
    @19
    @20
    wa
    @17
    wi
    @35
    @37
    @12
    cS
    cR
    @39
    @42
    zsubcld
    cP
    cA
    @16
    coprmdvds
    syl3anc
    mp2and
    @12
    cP
    cn
    wcel
    #
    @38
    @41
    @15
    @17
    wb
    @12
    @0
    @45
    @34
    cP
    prmnn
    syl
    #
    @39
    @42
    cS
    cR
    cP
    moddvds
    syl3anc
    mpbird
    @12
    cS
    cr
    wcel
    cP
    crp
    wcel
    #
    cc0
    cS
    cle
    wbr
    #
    cS
    cP
    clt
    wbr
    #
    @13
    cS
    wceq
    @44
    @12
    cP
    @46
    nnrpd
    #
    @6
    @48
    @3
    @9
    cS
    cc0
    @4
    elfzle1
    ad2antrl
    @12
    @49
    cS
    @4
    cle
    wbr
    #
    @6
    @51
    @3
    @9
    cS
    cc0
    @4
    elfzle2
    ad2antrl
    @12
    @38
    @31
    @49
    @51
    wb
    @39
    @35
    cS
    cP
    zltlem1
    syl2anc
    mpbird
    cS
    cP
    modid
    syl22anc
    @12
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
    cP
    cmo
    co
    #
    @54
    @14
    cR
    @12
    @53
    cr
    wcel
    @47
    @55
    @54
    wceq
    @12
    @53
    @12
    @1
    @52
    cn0
    wcel
    #
    @53
    cz
    wcel
    @37
    @12
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @56
    @34
    cP
    prmuz2
    c2
    cP
    uznn0sub
    3syl
    cA
    @52
    zexpcl
    syl2anc
    zred
    @50
    @53
    cP
    modabs2
    syl2anc
    cR
    @54
    cP
    cmo
    prmdiv.1
    oveq1i
    prmdiv.1
    3eqtr4g
    3eqtr3d
    ex
    @3
    @28
    @11
    @10
    @29
    @11
    @27
    @6
    @24
    @9
    @27
    @6
    @11
    cR
    @5
    wcel
    @26
    @5
    cR
    @26
    cc0
    c1
    caddc
    co
    #
    @4
    cfz
    co
    #
    @5
    c1
    @57
    @4
    cfz
    1e0p1
    oveq1i
    cc0
    cz
    wcel
    @58
    @5
    wss
    0z
    cc0
    @4
    fzp1ss
    ax-mp
    eqsstri
    sseli
    cS
    cR
    @5
    eleq1
    syl5ibr
    @11
    @9
    @24
    @11
    @8
    @22
    cP
    cdvds
    @11
    @7
    @21
    c1
    cmin
    cS
    cR
    cA
    cmul
    oveq2
    oveq1d
    breq2d
    biimprd
    anim12d
    syl5com
    impbid
end
