include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "wrex.mm"
include "cc0.mm"
include "wne.mm"
include "cgcd.mm"
include "eldifi.mm"
include "adantl.mm"
include "prmz.mm"
include "syl.mm"
include "simpl.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "wb.mm"
include "coprm.mm"
include "lgsne0.mm"
include "3bitr4d.mm"
include "necon4bbid.mm"
include "0ne1.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "syl6bi.mm"
include "necon2bd.mm"
include "lgsqrlem5.mm"
include "3expia.mm"
include "jcad.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "simprl.mm"
include "zred.mm"
include "absresq.mm"
include "oveq1d.mm"
include "cn.mm"
include "simplr.mm"
include "ad3antlr.mm"
include "zsqcl.mm"
include "simplll.mm"
include "simprr.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "mtbird.mm"
include "2nn.mm"
include "a1i.mm"
include "prmdvdsexp.mm"
include "syl3anc.mm"
include "mtbid.mm"
include "dvds0.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "nnabscl.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "dvdsabsb.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "lgssq.mm"
include "syl211anc.mm"
include "cmo.mm"
include "prmnn.mm"
include "moddvds.mm"
include "mpbird.mm"
include "eldifsni.mm"
include "necomd.mm"
include "cuz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "dvdsprm.mm"
include "necon3bbid.mm"
include "sylancr.mm"
include "lgsmod.mm"
include "3eqtr3d.mm"
include "3eqtr3rd.mm"
include "rexlimdvaa.mm"
include "expimpd.mm"
include "impbid.mm"

theorem lgsqr
  let vx: setvar x
  let cA: class A
  let cP: class P

  disjoint A x
  disjoint P x
  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) ) -> ( ( A /L P ) = 1 <-> ( -. P || A /\ E. x e. ZZ P || ( ( x ^ 2 ) - A ) ) ) )

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
    wa
    #
    cA
    cP
    clgs
    co
    #
    c1
    wceq
    #
    cP
    cA
    cdvds
    wbr
    #
    wn
    #
    cP
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cmin
    co
    cdvds
    wbr
    #
    vx
    cz
    wrex
    #
    wa
    @3
    @5
    @7
    @11
    @3
    @6
    @4
    c1
    @3
    @6
    @4
    cc0
    wceq
    #
    @4
    c1
    wne
    #
    @3
    @6
    @4
    cc0
    @3
    cP
    cA
    cgcd
    co
    #
    c1
    wceq
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
    @4
    cc0
    wne
    #
    @3
    @14
    @16
    c1
    @3
    cP
    cz
    wcel
    #
    @0
    @14
    @16
    wceq
    @3
    cP
    cprime
    wcel
    #
    @19
    @2
    @20
    @0
    cP
    cprime
    @1
    eldifi
    #
    adantl
    #
    cP
    prmz
    #
    syl
    #
    @0
    @2
    simpl
    #
    cP
    cA
    gcdcom
    syl2anc
    eqeq1d
    @3
    @20
    @0
    @7
    @15
    wb
    @22
    @25
    cP
    cA
    coprm
    syl2anc
    @3
    @0
    @19
    @18
    @17
    wb
    @25
    @24
    cA
    cP
    lgsne0
    syl2anc
    3bitr4d
    necon4bbid
    @12
    @13
    cc0
    c1
    wne
    0ne1
    @4
    cc0
    c1
    neeq1
    mpbiri
    syl6bi
    necon2bd
    @0
    @2
    @5
    @11
    vx
    cA
    cP
    lgsqrlem5
    3expia
    jcad
    @3
    @7
    @11
    @5
    @3
    @7
    wa
    #
    @10
    @5
    vx
    cz
    @26
    @8
    cz
    wcel
    #
    @10
    wa
    #
    wa
    #
    @8
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cP
    clgs
    co
    #
    @9
    cP
    clgs
    co
    #
    c1
    @4
    @29
    @31
    @9
    cP
    clgs
    @29
    @8
    cr
    wcel
    @31
    @9
    wceq
    @29
    @8
    @26
    @27
    @10
    simprl
    #
    zred
    @8
    absresq
    syl
    oveq1d
    @29
    @30
    cz
    wcel
    #
    @30
    cc0
    wne
    @19
    @30
    cP
    cgcd
    co
    #
    c1
    wceq
    @32
    c1
    wceq
    @29
    @30
    @29
    @27
    @8
    cc0
    wne
    #
    @30
    cn
    wcel
    @34
    @29
    cP
    @8
    cdvds
    wbr
    #
    wn
    @37
    @29
    cP
    @9
    cdvds
    wbr
    #
    @38
    @29
    @39
    @6
    @3
    @7
    @28
    simplr
    @29
    @19
    @9
    cz
    wcel
    #
    @0
    @10
    @39
    @6
    wb
    @29
    @20
    @19
    @2
    @20
    @0
    @7
    @28
    @21
    ad3antlr
    #
    @23
    syl
    #
    @29
    @27
    @40
    @34
    @8
    zsqcl
    syl
    #
    @0
    @2
    @7
    @28
    simplll
    #
    @26
    @27
    @10
    simprr
    #
    cP
    @9
    cA
    dvdssub2
    syl31anc
    mtbird
    @29
    @20
    @27
    c2
    cn
    wcel
    #
    @39
    @38
    wb
    @41
    @34
    @46
    @29
    2nn
    a1i
    @8
    cP
    c2
    prmdvdsexp
    syl3anc
    mtbid
    #
    @29
    @38
    @8
    cc0
    @29
    @38
    @8
    cc0
    wceq
    cP
    cc0
    cdvds
    wbr
    #
    @29
    @19
    @48
    @42
    cP
    dvds0
    syl
    @8
    cc0
    cP
    cdvds
    breq2
    syl5ibrcom
    necon3bd
    mpd
    @8
    nnabscl
    syl2anc
    #
    nnzd
    #
    @29
    @30
    @49
    nnne0d
    @42
    @29
    @36
    cP
    @30
    cgcd
    co
    #
    c1
    @29
    @35
    @19
    @36
    @51
    wceq
    @50
    @42
    @30
    cP
    gcdcom
    syl2anc
    @29
    cP
    @30
    cdvds
    wbr
    #
    wn
    #
    @51
    c1
    wceq
    #
    @29
    @38
    @52
    @47
    @29
    @19
    @27
    @38
    @52
    wb
    @42
    @34
    cP
    @8
    dvdsabsb
    syl2anc
    mtbid
    @29
    @20
    @35
    @53
    @54
    wb
    @41
    @50
    cP
    @30
    coprm
    syl2anc
    mpbid
    eqtrd
    @30
    cP
    lgssq
    syl211anc
    @29
    @9
    cP
    cmo
    co
    #
    cP
    clgs
    co
    #
    cA
    cP
    cmo
    co
    #
    cP
    clgs
    co
    #
    @33
    @4
    @29
    @55
    @57
    cP
    clgs
    @29
    @55
    @57
    wceq
    #
    @10
    @45
    @29
    cP
    cn
    wcel
    #
    @40
    @0
    @59
    @10
    wb
    @29
    @20
    @60
    @41
    cP
    prmnn
    syl
    #
    @43
    @44
    @9
    cA
    cP
    moddvds
    syl3anc
    mpbird
    oveq1d
    @29
    @40
    @60
    c2
    cP
    cdvds
    wbr
    #
    wn
    #
    @56
    @33
    wceq
    @43
    @61
    @29
    @63
    c2
    cP
    wne
    #
    @29
    cP
    c2
    @2
    cP
    c2
    wne
    @0
    @7
    @28
    cP
    cprime
    c2
    eldifsni
    ad3antlr
    necomd
    @29
    c2
    c2
    cuz
    cfv
    wcel
    #
    @20
    @63
    @64
    wb
    c2
    cz
    wcel
    @65
    2z
    c2
    uzid
    ax-mp
    @41
    @65
    @20
    wa
    @62
    c2
    cP
    cP
    c2
    dvdsprm
    necon3bbid
    sylancr
    mpbird
    #
    @9
    cP
    lgsmod
    syl3anc
    @29
    @0
    @60
    @63
    @58
    @4
    wceq
    @44
    @61
    @66
    cA
    cP
    lgsmod
    syl3anc
    3eqtr3d
    3eqtr3rd
    rexlimdvaa
    expimpd
    impbid
end
