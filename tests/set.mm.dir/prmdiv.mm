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
include "cfz.mm"
include "cmul.mm"
include "cc0.mm"
include "caddc.mm"
include "wceq.mm"
include "nprmdvds1.mm"
include "3ad2ant1.mm"
include "cphi.mm"
include "cfv.mm"
include "cexp.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmo.mm"
include "cn.mm"
include "cgcd.mm"
include "prmnn.mm"
include "simp2.mm"
include "prmz.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "coprm.mm"
include "biimp3a.mm"
include "eqtrd.mm"
include "eulerth.mm"
include "syl3anc.mm"
include "wb.mm"
include "cn0.mm"
include "phiprm.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "eqeltrd.mm"
include "zexpcl.mm"
include "1zzd.mm"
include "moddvds.mm"
include "mpbid.mm"
include "cuz.mm"
include "prmuz2.mm"
include "uznn0sub.mm"
include "zred.mm"
include "nndivred.mm"
include "flcld.mm"
include "zmulcld.mm"
include "dvdsmul1.mm"
include "wa.mm"
include "wi.mm"
include "1z.mm"
include "zsubcl.mm"
include "sylancl.mm"
include "dvds2sub.mm"
include "mp2and.mm"
include "zcnd.mm"
include "subdid.mm"
include "cr.mm"
include "crp.mm"
include "nnrpd.mm"
include "modval.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "nncnd.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "expp1d.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "mul12d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "sub32d.mm"
include "breqtrrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "cneg.mm"
include "mul01d.mm"
include "df-neg.mm"
include "dvdsnegb.mm"
include "bitr4d.mm"
include "sylibd.mm"
include "mtod.mm"
include "wo.mm"
include "zmodfz.mm"
include "syl5eqel.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfzp12.mm"
include "ord.mm"
include "mpd.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "jca.mm"

theorem prmdiv
  let cA: class A
  let cP: class P
  let cR: class R
  assume prmdiv.1: |- R = ( ( A ^ ( P - 2 ) ) mod P )


  assert |- ( ( P e. Prime /\ A e. ZZ /\ -. P || A ) -> ( R e. ( 1 ... ( P - 1 ) ) /\ P || ( ( A x. R ) - 1 ) ) )

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
    cR
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    cP
    cA
    cR
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
    @3
    cR
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
    @3
    cR
    cc0
    wceq
    #
    wn
    cR
    @10
    wcel
    #
    @3
    @11
    cP
    c1
    cdvds
    wbr
    #
    @0
    @1
    @13
    wn
    @2
    cP
    nprmdvds1
    3ad2ant1
    @3
    @11
    cP
    cA
    cc0
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
    @13
    @3
    @8
    @11
    @16
    @3
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
    cP
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
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @7
    cdvds
    @3
    cP
    @19
    cdvds
    wbr
    #
    cP
    @25
    cdvds
    wbr
    #
    cP
    @26
    cdvds
    wbr
    #
    @3
    @18
    cP
    cmo
    co
    c1
    cP
    cmo
    co
    wceq
    #
    @27
    @3
    cP
    cn
    wcel
    #
    @1
    cA
    cP
    cgcd
    co
    #
    c1
    wceq
    @30
    @0
    @1
    @31
    @2
    cP
    prmnn
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @3
    @32
    cP
    cA
    cgcd
    co
    #
    c1
    @3
    @1
    cP
    cz
    wcel
    #
    @32
    @35
    wceq
    @34
    @0
    @1
    @36
    @2
    cP
    prmz
    3ad2ant1
    #
    cA
    cP
    gcdcom
    syl2anc
    @0
    @1
    @2
    @35
    c1
    wceq
    cP
    cA
    coprm
    biimp3a
    eqtrd
    cA
    cP
    eulerth
    syl3anc
    @3
    @31
    @18
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @30
    @27
    wb
    @33
    @3
    @1
    @17
    cn0
    wcel
    @38
    @34
    @3
    @17
    @4
    cn0
    @0
    @1
    @17
    @4
    wceq
    @2
    cP
    phiprm
    3ad2ant1
    #
    @3
    @31
    @4
    cn0
    wcel
    @33
    cP
    nnm1nn0
    syl
    #
    eqeltrd
    cA
    @17
    zexpcl
    syl2anc
    #
    @3
    1zzd
    @18
    c1
    cP
    moddvds
    syl3anc
    mpbid
    @3
    @36
    @24
    cz
    wcel
    @28
    @37
    @3
    cA
    @23
    @34
    @3
    @22
    @3
    @21
    cP
    @3
    @21
    @3
    @1
    @20
    cn0
    wcel
    #
    @21
    cz
    wcel
    #
    @34
    @3
    cP
    c2
    cuz
    cfv
    wcel
    #
    @43
    @0
    @1
    @45
    @2
    cP
    prmuz2
    3ad2ant1
    c2
    cP
    uznn0sub
    syl
    #
    cA
    @20
    zexpcl
    syl2anc
    #
    zred
    #
    @33
    nndivred
    flcld
    #
    zmulcld
    #
    cP
    @24
    dvdsmul1
    syl2anc
    @3
    @36
    @19
    cz
    wcel
    #
    @25
    cz
    wcel
    @27
    @28
    wa
    @29
    wi
    @37
    @3
    @38
    @39
    @51
    @42
    1z
    @18
    c1
    zsubcl
    sylancl
    @3
    cP
    @24
    @37
    @50
    zmulcld
    #
    cP
    @19
    @25
    dvds2sub
    syl3anc
    mp2and
    @3
    @7
    @18
    @25
    cmin
    co
    #
    c1
    cmin
    co
    @26
    @3
    @6
    @53
    c1
    cmin
    @3
    cA
    @21
    cP
    @23
    cmul
    co
    #
    cmin
    co
    #
    cmul
    co
    cA
    @21
    cmul
    co
    #
    cA
    @54
    cmul
    co
    #
    cmin
    co
    @6
    @53
    @3
    cA
    @21
    @54
    @3
    cA
    @34
    zcnd
    #
    @3
    @21
    @47
    zcnd
    #
    @3
    @54
    @3
    cP
    @23
    @37
    @49
    zmulcld
    zcnd
    subdid
    @3
    cR
    @55
    cA
    cmul
    @3
    cR
    @21
    cP
    cmo
    co
    #
    @55
    prmdiv.1
    @3
    @21
    cr
    wcel
    cP
    crp
    wcel
    @60
    @55
    wceq
    @48
    @3
    cP
    @33
    nnrpd
    @21
    cP
    modval
    syl2anc
    syl5eq
    oveq2d
    @3
    @18
    @56
    @25
    @57
    cmin
    @3
    @18
    cA
    @20
    c1
    caddc
    co
    #
    cexp
    co
    @21
    cA
    cmul
    co
    @56
    @3
    @17
    @61
    cA
    cexp
    @3
    @17
    cP
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @61
    @3
    @17
    @4
    @63
    @40
    @62
    c1
    cP
    cmin
    2m1e1
    oveq2i
    syl6eqr
    @3
    cP
    c2
    c1
    @3
    cP
    @33
    nncnd
    #
    @3
    2cnd
    @3
    1cnd
    #
    subsubd
    eqtrd
    oveq2d
    @3
    cA
    @20
    @58
    @46
    expp1d
    @3
    @21
    cA
    @59
    @58
    mulcomd
    3eqtrd
    @3
    cP
    cA
    @23
    @64
    @58
    @3
    @23
    @49
    zcnd
    mul12d
    oveq12d
    3eqtr4d
    oveq1d
    @3
    @18
    @25
    c1
    @3
    @18
    @42
    zcnd
    @3
    @25
    @52
    zcnd
    @65
    sub32d
    eqtrd
    breqtrrd
    #
    @11
    @7
    @15
    cP
    cdvds
    @11
    @6
    @14
    c1
    cmin
    cR
    cc0
    cA
    cmul
    oveq2
    oveq1d
    breq2d
    syl5ibcom
    @3
    @16
    cP
    c1
    cneg
    #
    cdvds
    wbr
    #
    @13
    @3
    @15
    @67
    cP
    cdvds
    @3
    @15
    cc0
    c1
    cmin
    co
    @67
    @3
    @14
    cc0
    c1
    cmin
    @3
    cA
    @58
    mul01d
    oveq1d
    c1
    df-neg
    syl6eqr
    breq2d
    @3
    @36
    @39
    @13
    @68
    wb
    @37
    1z
    cP
    c1
    dvdsnegb
    sylancl
    bitr4d
    sylibd
    mtod
    @3
    @11
    @12
    @3
    cR
    cc0
    @4
    cfz
    co
    #
    wcel
    #
    @11
    @12
    wo
    #
    @3
    cR
    @60
    @69
    prmdiv.1
    @3
    @44
    @31
    @60
    @69
    wcel
    @47
    @33
    @21
    cP
    zmodfz
    syl2anc
    syl5eqel
    @3
    @4
    cc0
    cuz
    cfv
    #
    wcel
    @70
    @71
    wb
    @3
    @4
    cn0
    @72
    @41
    nn0uz
    syl6eleq
    cR
    cc0
    @4
    elfzp12
    syl
    mpbid
    ord
    mpd
    c1
    @9
    @4
    cfz
    1e0p1
    oveq1i
    syl6eleqr
    @66
    jca
end
