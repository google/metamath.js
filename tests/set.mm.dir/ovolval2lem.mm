include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "c1.mm"
include "cseq.mm"
include "cn.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cico.mm"
include "cfv.mm"
include "cvol.mm"
include "csu.mm"
include "cmpt.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "wcel.mm"
include "wceq.mm"
include "cle.mm"
include "cin.mm"
include "cvv.mm"
include "wss.mm"
include "reex.mm"
include "xpex.mm"
include "inss2.mm"
include "mapss.mm"
include "mp2an.mm"
include "wf.mm"
include "inex2.mm"
include "a1i.mm"
include "nnex.mm"
include "elmapd.mm"
include "mpbird.mm"
include "sseldi.mm"
include "1zzd.mm"
include "nnuz.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "elmapi.mm"
include "adantr.mm"
include "simpr.mm"
include "fvovco.mm"
include "fveq2d.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "volicore.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "eqid.mm"
include "fsumsermpt.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "iftrued.mm"
include "wn.mm"
include "sylan.mm"
include "cxr.mm"
include "ressxr.mm"
include "cop.mm"
include "xpss.mm"
include "1st2ndb.mm"
include "sylib.mm"
include "eqcomd.mm"
include "inss1.mm"
include "fssd.mm"
include "df-br.mm"
include "sylibr.mm"
include "lenltd.mm"
include "xrletrid.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "simp2.mm"
include "eqleltd.mm"
include "mpbid.mm"
include "simprd.mm"
include "iffalsed.mm"
include "subeq0bd.mm"
include "eqtr4d.mm"
include "syl3anc.mm"
include "pm2.61dan.mm"
include "volico.mm"
include "abssuble0d.mm"
include "3eqtr4d.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "cc.mm"
include "cnmetdval.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "rr2sscn2.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "fcomptss.mm"
include "seqeq3d.mm"
include "eqtr2d.mm"
include "rneqd.mm"

theorem ovolval2lem
  let wph: wff ph
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vx: setvar x
  assume ovolval2lem.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )

  disjoint F k
  disjoint F n
  disjoint k n
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ran seq 1 ( + , ( ( abs o. - ) o. F ) ) = ran ( n e. NN |-> sum_ k e. ( 1 ... n ) ( vol ` ( ( [,) o. F ) ` k ) ) ) )

  proof
    wph
    caddc
    cabs
    cmin
    ccom
    #
    cF
    ccom
    #
    c1
    cseq
    #
    vn
    cn
    c1
    vn
    cv
    cfz
    co
    vk
    cv
    #
    cico
    cF
    ccom
    cfv
    #
    cvol
    cfv
    #
    vk
    csu
    cmpt
    #
    wph
    @6
    caddc
    vk
    cn
    @5
    cmpt
    #
    c1
    cseq
    #
    @2
    wph
    cF
    cr
    cr
    cxp
    #
    cn
    cmap
    co
    #
    wcel
    #
    @6
    @8
    wceq
    wph
    cle
    @9
    cin
    #
    cn
    cmap
    co
    #
    @10
    cF
    @9
    cvv
    wcel
    @12
    @9
    wss
    @13
    @10
    wss
    cr
    cr
    reex
    reex
    xpex
    #
    cle
    @9
    inss2
    @12
    @9
    cn
    cvv
    mapss
    mp2an
    wph
    cF
    @13
    wcel
    cn
    @12
    cF
    wf
    ovolval2lem.1
    wph
    @12
    cn
    cF
    cvv
    cvv
    @12
    cvv
    wcel
    wph
    @9
    cle
    @14
    inex2
    a1i
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    elmapd
    mpbird
    sseldi
    #
    @11
    @5
    vk
    vn
    @6
    @8
    c1
    cn
    @11
    1zzd
    nnuz
    @11
    @3
    cn
    wcel
    #
    wa
    #
    @5
    @17
    @5
    @3
    cF
    cfv
    #
    c1st
    cfv
    #
    @18
    c2nd
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    cr
    @17
    @4
    @21
    cvol
    @17
    cF
    cico
    cr
    cr
    cn
    @3
    @11
    cn
    @9
    cF
    wf
    #
    @16
    cF
    @9
    cn
    elmapi
    #
    adantr
    @11
    @16
    simpr
    fvovco
    fveq2d
    #
    @17
    @19
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    @22
    cr
    wcel
    @17
    @18
    @9
    wcel
    #
    @26
    @11
    cn
    @9
    @3
    cF
    @24
    ffvelrnda
    #
    @18
    cr
    cr
    xp1st
    syl
    #
    @17
    @28
    @27
    @29
    @18
    cr
    cr
    xp2nd
    syl
    #
    @19
    @20
    volicore
    syl2anc
    eqeltrd
    recnd
    @6
    eqid
    @8
    eqid
    fsumsermpt
    syl
    wph
    @7
    @1
    caddc
    c1
    wph
    @7
    vk
    cn
    @18
    @0
    cfv
    #
    cmpt
    @1
    wph
    vk
    cn
    @5
    @32
    wph
    @16
    wa
    #
    @22
    @19
    @20
    cmin
    co
    cabs
    cfv
    #
    @5
    @32
    @33
    @19
    @20
    clt
    wbr
    #
    @20
    @19
    cmin
    co
    #
    cc0
    cif
    #
    @36
    @22
    @34
    @33
    @35
    @37
    @36
    wceq
    #
    @33
    @35
    wa
    @35
    @36
    cc0
    @33
    @35
    simpr
    iftrued
    @33
    @35
    wn
    #
    wa
    #
    @26
    @27
    @19
    @20
    wceq
    #
    @38
    @33
    @26
    @39
    wph
    @11
    @16
    @26
    @15
    @30
    sylan
    #
    adantr
    #
    @33
    @27
    @39
    wph
    @11
    @16
    @27
    @15
    @31
    sylan
    #
    adantr
    #
    @40
    @19
    @20
    @40
    cr
    cxr
    @19
    ressxr
    @43
    sseldi
    @40
    cr
    cxr
    @20
    ressxr
    @45
    sseldi
    @33
    @19
    @20
    cle
    wbr
    #
    @39
    @33
    @19
    @20
    cop
    #
    cle
    wcel
    @46
    @33
    @47
    @18
    cle
    @33
    @18
    @47
    wph
    @11
    @16
    @18
    @47
    wceq
    #
    @15
    @17
    @18
    cvv
    cvv
    cxp
    #
    wcel
    @48
    @17
    @9
    @49
    @18
    cr
    cr
    xpss
    @29
    sseldi
    @18
    1st2ndb
    sylib
    #
    sylan
    eqcomd
    wph
    cn
    cle
    @3
    cF
    wph
    cn
    @12
    cle
    cF
    ovolval2lem.1
    @12
    cle
    wss
    wph
    cle
    @9
    inss1
    a1i
    fssd
    ffvelrnda
    eqeltrd
    @19
    @20
    cle
    df-br
    sylibr
    #
    adantr
    @40
    @20
    @19
    cle
    wbr
    @39
    @33
    @39
    simpr
    @40
    @20
    @19
    @45
    @43
    lenltd
    mpbird
    xrletrid
    @26
    @27
    @41
    w3a
    #
    @37
    cc0
    @36
    @52
    @35
    @36
    cc0
    @52
    @46
    @39
    @52
    @41
    @46
    @39
    wa
    @26
    @27
    @41
    simp3
    #
    @52
    @19
    @20
    @26
    @27
    @41
    simp1
    @26
    @27
    @41
    simp2
    #
    eqleltd
    mpbid
    simprd
    iffalsed
    @52
    @20
    @19
    @52
    @20
    @54
    recnd
    @52
    @19
    @20
    @53
    eqcomd
    subeq0bd
    eqtr4d
    syl3anc
    pm2.61dan
    @33
    @26
    @27
    @22
    @37
    wceq
    @42
    @44
    @19
    @20
    volico
    syl2anc
    @33
    @19
    @20
    @42
    @44
    @51
    abssuble0d
    3eqtr4d
    @33
    @11
    @16
    @5
    @22
    wceq
    wph
    @11
    @16
    @15
    adantr
    #
    wph
    @16
    simpr
    #
    @25
    syl2anc
    @33
    @11
    @16
    @32
    @34
    wceq
    @55
    @56
    @17
    @32
    @47
    @0
    cfv
    #
    @19
    @20
    @0
    co
    #
    @34
    @17
    @18
    @47
    @0
    @50
    fveq2d
    @57
    @58
    wceq
    @17
    @58
    @57
    @19
    @20
    @0
    df-ov
    eqcomi
    a1i
    @17
    @19
    cc
    wcel
    @20
    cc
    wcel
    @58
    @34
    wceq
    @17
    @19
    @30
    recnd
    @17
    @20
    @31
    recnd
    @19
    @20
    @0
    @0
    eqid
    cnmetdval
    syl2anc
    3eqtrd
    syl2anc
    3eqtr4d
    mpteq2dva
    wph
    vk
    cn
    @9
    cc
    cc
    cxp
    #
    cr
    cF
    @0
    wph
    @11
    @23
    @15
    @24
    syl
    @9
    @59
    wss
    wph
    rr2sscn2
    a1i
    @59
    cr
    @0
    wf
    #
    wph
    cc
    cr
    cabs
    wf
    @59
    cc
    cmin
    wf
    @60
    absf
    subf
    @59
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    a1i
    fcomptss
    eqtr4d
    seqeq3d
    eqtr2d
    rneqd
end
