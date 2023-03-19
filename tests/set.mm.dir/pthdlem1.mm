include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cvv.mm"
include "wf.mm"
include "wf1.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cc0.mm"
include "cword.mm"
include "wcel.mm"
include "wrdf.mm"
include "syl.mm"
include "fzo0ss1.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq2d.mm"
include "syl5sseq.mm"
include "cz.mm"
include "wss.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0z.mm"
include "3syl.mm"
include "fzossrbm1.mm"
include "sstrd.mm"
include "fssresd.mm"
include "adantr.mm"
include "csn.mm"
include "cun.mm"
include "cn.mm"
include "cle.mm"
include "nn0re.mm"
include "ltm1d.mm"
include "cr.mm"
include "1re.mm"
include "peano2rem.mm"
include "lttr.mm"
include "mp3an2i.mm"
include "1red.mm"
include "ltle.mm"
include "syl2anc.mm"
include "syld.mm"
include "mpan2d.mm"
include "imdistani.mm"
include "elnnnn0c.mm"
include "sylibr.mm"
include "sylan.mm"
include "fzo0sn0fzo1.mm"
include "caddc.mm"
include "cuz.mm"
include "1zzd.mm"
include "c2.mm"
include "1p1e2.mm"
include "2z.mm"
include "eqeltri.mm"
include "wb.mm"
include "w3a.mm"
include "ltaddsub.mm"
include "bicomd.mm"
include "2re.mm"
include "sylancr.mm"
include "sylbid.mm"
include "imp.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzosplitsnm1.mm"
include "uneq2d.mm"
include "eqtrd.mm"
include "raleqdv.mm"
include "ralunb.mm"
include "anbi2i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "raleqi.mm"
include "fvres.mm"
include "eqcomd.mm"
include "adantl.mm"
include "neeq12d.mm"
include "biimpd.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "syl5bi.mm"
include "adantrd.mm"
include "adantld.mm"
include "mpd.mm"
include "dff14a.mm"
include "sylanbrc.mm"
include "df-f1.mm"
include "sylib.mm"
include "simprd.mm"
include "wn.mm"
include "c0.mm"
include "funcnv0.mm"
include "nn0zd.mm"
include "peano2zm.mm"
include "zred.mm"
include "lenltd.mm"
include "biimpar.mm"
include "syl5eqbr.mm"
include "syl5eqel.mm"
include "jca.mm"
include "fzon.mm"
include "mpbird.mm"
include "reseq2d.mm"
include "res0.mm"
include "syl6eq.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "pm2.61dan.mm"

theorem pthdlem1
  let wph: wff ph
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  assume pthd.p: |- ( ph -> P e. Word _V )
  assume pthd.r: |- R = ( ( # ` P ) - 1 )
  assume pthd.s: |- ( ph -> A. i e. ( 0 ..^ ( # ` P ) ) A. j e. ( 1 ..^ R ) ( i =/= j -> ( P ` i ) =/= ( P ` j ) ) )

  disjoint P i
  disjoint P j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> Fun `' ( P |` ( 1 ..^ R ) ) )

  proof
    wph
    c1
    cP
    chash
    cfv
    #
    c1
    cmin
    co
    #
    clt
    wbr
    #
    cP
    c1
    cR
    cfzo
    co
    #
    cres
    #
    ccnv
    #
    wfun
    #
    wph
    @2
    wa
    #
    @3
    cvv
    @4
    wf
    #
    @6
    @7
    @3
    cvv
    @4
    wf1
    #
    @8
    @6
    wa
    @7
    @8
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @10
    @4
    cfv
    #
    @11
    @4
    cfv
    #
    wne
    #
    wi
    #
    vj
    @3
    wral
    #
    vi
    @3
    wral
    #
    @9
    wph
    @8
    @2
    wph
    cc0
    @0
    cfzo
    co
    #
    cvv
    @3
    cP
    wph
    cP
    cvv
    cword
    wcel
    #
    @19
    cvv
    cP
    wf
    pthd.p
    cvv
    cP
    wrdf
    syl
    wph
    @3
    cc0
    @1
    cfzo
    co
    #
    @19
    wph
    cc0
    cR
    cfzo
    co
    @3
    @21
    cR
    fzo0ss1
    wph
    cR
    @1
    cc0
    cfzo
    cR
    @1
    wceq
    wph
    pthd.r
    a1i
    oveq2d
    syl5sseq
    wph
    @0
    cz
    wcel
    #
    @21
    @19
    wss
    wph
    @20
    @0
    cn0
    wcel
    #
    @22
    pthd.p
    cvv
    cP
    lencl
    #
    @0
    nn0z
    #
    3syl
    @0
    fzossrbm1
    syl
    sstrd
    fssresd
    adantr
    @7
    @12
    @10
    cP
    cfv
    #
    @11
    cP
    cfv
    #
    wne
    #
    wi
    #
    vj
    @3
    wral
    #
    vi
    @19
    wral
    #
    @18
    wph
    @31
    @2
    pthd.s
    adantr
    @7
    @31
    @30
    vi
    cc0
    csn
    #
    wral
    #
    @30
    vi
    c1
    @1
    cfzo
    co
    #
    wral
    #
    @30
    vi
    @1
    csn
    #
    wral
    #
    wa
    #
    wa
    #
    @18
    @7
    @31
    @30
    vi
    @32
    @34
    @36
    cun
    #
    cun
    #
    wral
    #
    @39
    @7
    @30
    vi
    @19
    @41
    @7
    @19
    @32
    c1
    @0
    cfzo
    co
    #
    cun
    #
    @41
    @7
    @0
    cn
    wcel
    #
    @19
    @44
    wceq
    wph
    @23
    @2
    @45
    wph
    @20
    @23
    pthd.p
    @24
    syl
    #
    @23
    @2
    wa
    #
    @23
    c1
    @0
    cle
    wbr
    #
    wa
    @45
    @23
    @2
    @48
    @23
    @2
    @1
    @0
    clt
    wbr
    #
    @48
    @23
    @0
    @0
    nn0re
    #
    ltm1d
    @23
    @2
    @49
    wa
    #
    c1
    @0
    clt
    wbr
    #
    @48
    c1
    cr
    wcel
    #
    @23
    @1
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @51
    @52
    wi
    1re
    @23
    @55
    @54
    @50
    @0
    peano2rem
    syl
    @50
    c1
    @1
    @0
    lttr
    mp3an2i
    @23
    @53
    @55
    @52
    @48
    wi
    @23
    1red
    #
    @50
    c1
    @0
    ltle
    syl2anc
    syld
    mpan2d
    imdistani
    @0
    elnnnn0c
    sylibr
    sylan
    @0
    fzo0sn0fzo1
    syl
    @7
    @43
    @40
    @32
    @7
    c1
    cz
    wcel
    #
    @0
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    @43
    @40
    wceq
    @7
    1zzd
    wph
    @23
    @2
    @59
    @46
    @47
    @58
    cz
    wcel
    #
    @22
    @58
    @0
    cle
    wbr
    #
    @59
    @60
    @47
    @58
    c2
    cz
    1p1e2
    2z
    eqeltri
    a1i
    @23
    @22
    @2
    @25
    adantr
    @23
    @2
    @61
    @23
    @2
    @58
    @0
    clt
    wbr
    #
    @61
    @53
    @23
    @53
    @55
    @2
    @62
    wb
    1re
    @56
    @50
    @53
    @53
    @55
    w3a
    @62
    @2
    c1
    c1
    @0
    ltaddsub
    bicomd
    mp3an2i
    @23
    @58
    cr
    wcel
    @55
    @62
    @61
    wi
    @58
    c2
    cr
    1p1e2
    2re
    eqeltri
    @50
    @58
    @0
    ltle
    sylancr
    sylbid
    imp
    @58
    @0
    eluz2
    syl3anbrc
    sylan
    c1
    @0
    fzosplitsnm1
    syl2anc
    uneq2d
    eqtrd
    raleqdv
    @42
    @33
    @30
    vi
    @40
    wral
    #
    wa
    @39
    @30
    vi
    @32
    @40
    ralunb
    @63
    @38
    @33
    @30
    vi
    @34
    @36
    ralunb
    anbi2i
    bitri
    syl6bb
    @7
    @38
    @18
    @33
    @7
    @35
    @18
    @37
    @35
    @30
    vi
    @3
    wral
    @7
    @18
    @30
    vi
    @34
    @3
    @1
    cR
    c1
    cfzo
    cR
    @1
    pthd.r
    eqcomi
    oveq2i
    raleqi
    @7
    @30
    @17
    vi
    @3
    @7
    @10
    @3
    wcel
    #
    wa
    #
    @29
    @16
    vj
    @3
    @65
    @11
    @3
    wcel
    #
    wa
    #
    @28
    @15
    @12
    @67
    @28
    @15
    @67
    @26
    @13
    @27
    @14
    @65
    @26
    @13
    wceq
    #
    @66
    @64
    @68
    @7
    @64
    @13
    @26
    @10
    @3
    cP
    fvres
    eqcomd
    adantl
    adantr
    @66
    @27
    @14
    wceq
    @65
    @66
    @14
    @27
    @11
    @3
    cP
    fvres
    eqcomd
    adantl
    neeq12d
    biimpd
    imim2d
    ralimdva
    ralimdva
    syl5bi
    adantrd
    adantld
    sylbid
    mpd
    vi
    vj
    @3
    cvv
    @4
    dff14a
    sylanbrc
    @3
    cvv
    @4
    df-f1
    sylib
    simprd
    wph
    @2
    wn
    #
    wa
    #
    @6
    c0
    ccnv
    #
    wfun
    funcnv0
    @70
    @5
    @71
    @70
    @4
    c0
    @70
    @4
    cP
    c0
    cres
    c0
    @70
    @3
    c0
    cP
    @70
    @3
    c0
    wceq
    #
    cR
    c1
    cle
    wbr
    #
    @70
    cR
    @1
    c1
    cle
    pthd.r
    wph
    @1
    c1
    cle
    wbr
    @69
    wph
    @1
    c1
    wph
    @1
    wph
    @22
    @1
    cz
    wcel
    wph
    @0
    @46
    nn0zd
    @0
    peano2zm
    syl
    #
    zred
    wph
    1red
    lenltd
    biimpar
    syl5eqbr
    @70
    @57
    cR
    cz
    wcel
    #
    wa
    #
    @72
    @73
    wb
    wph
    @76
    @69
    wph
    @57
    @75
    wph
    1zzd
    wph
    cR
    @1
    cz
    pthd.r
    @74
    syl5eqel
    jca
    adantr
    @76
    @73
    @72
    c1
    cR
    fzon
    bicomd
    syl
    mpbird
    reseq2d
    cP
    res0
    syl6eq
    cnveqd
    funeqd
    mpbiri
    pm2.61dan
end
