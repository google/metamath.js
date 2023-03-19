include "c0.mm"
include "wceq.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "wcel.mm"
include "wss.mm"
include "infxrcl.mm"
include "syl.mm"
include "pnfge.mm"
include "adantr.mm"
include "infeq1.mm"
include "xrinf0.mm"
include "a1i.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cmnf.mm"
include "cv.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "id.mm"
include "2re.mm"
include "resubcld.mm"
include "simpr.mm"
include "wb.mm"
include "infxrunb2.mm"
include "mpbird.mm"
include "breq2.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "wi.mm"
include "w3a.mm"
include "c1.mm"
include "cxad.mm"
include "crp.mm"
include "simpl.mm"
include "1rp.mm"
include "1ex.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "3adant3.mm"
include "simp1l.mm"
include "ad2antrr.mm"
include "simp1r.mm"
include "simp2.mm"
include "simpll3.mm"
include "simplr.mm"
include "infleinflem2.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "ralrimiva.mm"
include "mpbid.mm"
include "eqtr4d.mm"
include "xreqled.mm"
include "mnfxr.mm"
include "mnfle.mm"
include "necomd.mm"
include "xrleneltd.mm"
include "cdiv.mm"
include "nfv.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "infxrbnd2.mm"
include "ad4ant13.mm"
include "rphalfcld.mm"
include "infrpge.mm"
include "simpll.mm"
include "rphalfcl.mm"
include "ad2antlr.mm"
include "ovex.mm"
include "simp11l.mm"
include "simp11.mm"
include "simprd.mm"
include "simp12.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "infleinflem1.mm"
include "ad4ant14.mm"
include "xrlexaddrp.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem infleinf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vr: setvar r
  let vw: setvar w
  let vb: setvar b
  assume infleinf.a: |- ( ph -> A C_ RR* )
  assume infleinf.b: |- ( ph -> B C_ RR* )
  assume infleinf.c: |- ( ( ph /\ x e. B /\ y e. RR+ ) -> E. z e. A z <_ ( x +e y ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A r
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B b
  disjoint B w
  disjoint b w
  disjoint b x
  disjoint B r
  disjoint b ph
  disjoint ph w
  disjoint ph r
  assert |- ( ph -> inf ( A , RR* , < ) <_ inf ( B , RR* , < ) )

  proof
    wph
    cB
    c0
    wceq
    #
    cA
    cxr
    clt
    cinf
    #
    cB
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    wph
    @0
    wa
    @1
    cpnf
    @2
    cle
    wph
    @1
    cpnf
    cle
    wbr
    #
    @0
    wph
    @1
    cxr
    wcel
    #
    @4
    wph
    cA
    cxr
    wss
    #
    @5
    infleinf.a
    cA
    infxrcl
    syl
    #
    @1
    pnfge
    syl
    adantr
    @0
    cpnf
    @2
    wceq
    wph
    @0
    @2
    cpnf
    @0
    @2
    c0
    cxr
    clt
    cinf
    #
    cpnf
    cxr
    cB
    c0
    clt
    infeq1
    @8
    cpnf
    wceq
    @0
    xrinf0
    a1i
    eqtrd
    eqcomd
    adantl
    breqtrd
    wph
    @0
    wn
    #
    cB
    c0
    wne
    #
    @3
    @9
    @10
    wph
    cB
    c0
    neqne
    adantl
    wph
    @10
    wa
    #
    @2
    cmnf
    wceq
    #
    @3
    wph
    @12
    @3
    @10
    wph
    @12
    wa
    #
    @1
    @2
    wph
    @5
    @12
    @7
    adantr
    @13
    @1
    cmnf
    @2
    @13
    vz
    cv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    vr
    cr
    wral
    #
    @1
    cmnf
    wceq
    #
    @13
    @17
    vr
    cr
    @13
    @15
    cr
    wcel
    #
    wa
    #
    vx
    cv
    #
    @15
    c2
    cmin
    co
    #
    clt
    wbr
    #
    vx
    cB
    wrex
    #
    @17
    @21
    @23
    cr
    wcel
    #
    @22
    vy
    cv
    #
    clt
    wbr
    #
    vx
    cB
    wrex
    #
    vy
    cr
    wral
    #
    @25
    @20
    @26
    @13
    @20
    @15
    c2
    @20
    id
    c2
    cr
    wcel
    @20
    2re
    a1i
    resubcld
    adantl
    @13
    @30
    @20
    @13
    @30
    @12
    wph
    @12
    simpr
    #
    wph
    @30
    @12
    wb
    #
    @12
    wph
    cB
    cxr
    wss
    #
    @32
    infleinf.b
    vy
    vx
    cB
    infxrunb2
    syl
    adantr
    mpbird
    adantr
    @29
    @25
    vy
    @23
    cr
    @27
    @23
    wceq
    @28
    @24
    vx
    cB
    @27
    @23
    @22
    clt
    breq2
    rexbidv
    rspcva
    syl2anc
    @21
    @24
    @17
    vx
    cB
    wph
    @20
    @22
    cB
    wcel
    #
    @24
    @17
    wi
    wi
    @12
    wph
    @20
    wa
    #
    @34
    @24
    @17
    @35
    @34
    @24
    w3a
    #
    @14
    @22
    c1
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    @17
    @35
    @34
    @39
    @24
    wph
    @34
    @39
    @20
    wph
    @34
    wa
    #
    wph
    @34
    c1
    crp
    wcel
    #
    @39
    wph
    @34
    simpl
    wph
    @34
    simpr
    @41
    @40
    1rp
    a1i
    wph
    @34
    @27
    crp
    wcel
    #
    w3a
    #
    @14
    @22
    @27
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    wph
    @34
    @41
    w3a
    #
    @39
    wi
    vy
    c1
    1ex
    @27
    c1
    wceq
    #
    @43
    @48
    @46
    @39
    @49
    @42
    @41
    wph
    @34
    @27
    c1
    crp
    eleq1
    3anbi3d
    @49
    @45
    @38
    vz
    cA
    @49
    @44
    @37
    @14
    cle
    @27
    c1
    @22
    cxad
    oveq2
    breq2d
    rexbidv
    imbi12d
    infleinf.c
    vtocl
    syl3anc
    adantlr
    3adant3
    @36
    @38
    @16
    vz
    cA
    @36
    @14
    cA
    wcel
    #
    wa
    #
    @38
    @16
    @51
    @38
    wa
    #
    cA
    cB
    @15
    @22
    @14
    @52
    wph
    @6
    @36
    wph
    @50
    @38
    wph
    @20
    @34
    @24
    simp1l
    ad2antrr
    #
    infleinf.a
    syl
    @52
    wph
    @33
    @53
    infleinf.b
    syl
    @36
    @20
    @50
    @38
    wph
    @20
    @34
    @24
    simp1r
    ad2antrr
    @36
    @34
    @50
    @38
    @35
    @34
    @24
    simp2
    ad2antrr
    @35
    @34
    @24
    @50
    @38
    simpll3
    @36
    @50
    @38
    simplr
    @51
    @38
    simpr
    infleinflem2
    ex
    reximdva
    mpd
    3exp
    adantlr
    rexlimdv
    mpd
    ralrimiva
    wph
    @18
    @19
    wb
    #
    @12
    wph
    @6
    @54
    infleinf.a
    vr
    vz
    cA
    infxrunb2
    syl
    adantr
    mpbid
    @31
    eqtr4d
    xreqled
    adantlr
    @11
    @12
    wn
    #
    cmnf
    @2
    clt
    wbr
    #
    @3
    @11
    @55
    wa
    #
    cmnf
    @2
    wph
    cmnf
    cxr
    wcel
    #
    @10
    @55
    @58
    wph
    mnfxr
    a1i
    ad2antrr
    wph
    @2
    cxr
    wcel
    #
    @10
    @55
    wph
    @33
    @59
    infleinf.b
    cB
    infxrcl
    syl
    #
    ad2antrr
    #
    @57
    @59
    cmnf
    @2
    cle
    wbr
    @61
    @2
    mnfle
    syl
    @55
    cmnf
    @2
    wne
    @11
    @55
    @2
    cmnf
    @2
    cmnf
    neqne
    necomd
    adantl
    xrleneltd
    @11
    @56
    wa
    #
    vw
    @1
    @2
    wph
    @5
    @10
    @56
    @7
    ad2antrr
    wph
    @59
    @10
    @56
    @60
    ad2antrr
    @62
    vw
    cv
    #
    crp
    wcel
    #
    wa
    #
    @22
    @2
    @63
    c2
    cdiv
    co
    #
    cxad
    co
    cle
    wbr
    #
    vx
    cB
    wrex
    #
    @1
    @2
    @63
    cxad
    co
    cle
    wbr
    #
    @65
    vb
    vx
    vx
    cB
    @66
    @65
    vb
    nfv
    wph
    @33
    @10
    @56
    @64
    infleinf.b
    ad3antrrr
    wph
    @10
    @56
    @64
    simpllr
    wph
    @56
    vb
    cv
    @22
    cle
    wbr
    vx
    cB
    wral
    vb
    cr
    wrex
    #
    @10
    @64
    wph
    @56
    wa
    @70
    @56
    wph
    @56
    simpr
    wph
    @70
    @56
    wb
    #
    @56
    wph
    @33
    @71
    infleinf.b
    vb
    vx
    cB
    infxrbnd2
    syl
    adantr
    mpbird
    ad4ant13
    @65
    @63
    @62
    @64
    simpr
    rphalfcld
    infrpge
    wph
    @64
    @68
    @69
    wi
    @10
    @56
    wph
    @64
    wa
    #
    @67
    @69
    vx
    cB
    @72
    @34
    @67
    @69
    @72
    @34
    @67
    w3a
    #
    @14
    @22
    @66
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    @69
    @72
    @34
    @76
    @67
    @72
    @34
    wa
    wph
    @34
    @66
    crp
    wcel
    #
    @76
    wph
    @64
    @34
    simpll
    @72
    @34
    simpr
    @64
    @77
    wph
    @34
    @63
    rphalfcl
    ad2antlr
    @47
    wph
    @34
    @77
    w3a
    #
    @76
    wi
    vy
    @66
    @63
    c2
    cdiv
    ovex
    @27
    @66
    wceq
    #
    @43
    @78
    @46
    @76
    @79
    @42
    @77
    wph
    @34
    @27
    @66
    crp
    eleq1
    3anbi3d
    @79
    @45
    @75
    vz
    cA
    @79
    @44
    @74
    @14
    cle
    @27
    @66
    @22
    cxad
    oveq2
    breq2d
    rexbidv
    imbi12d
    infleinf.c
    vtocl
    syl3anc
    3adant3
    @73
    @75
    @69
    vz
    cA
    @73
    @50
    @75
    @69
    @73
    @50
    @75
    w3a
    #
    cA
    cB
    @63
    @22
    @14
    @80
    wph
    @6
    wph
    @64
    @34
    @67
    @50
    @75
    simp11l
    #
    infleinf.a
    syl
    @80
    wph
    @33
    @81
    infleinf.b
    syl
    @80
    wph
    @64
    @72
    @34
    @67
    @50
    @75
    simp11
    simprd
    @72
    @34
    @67
    @50
    @75
    simp12
    @73
    @50
    @67
    @75
    @72
    @34
    @67
    simp3
    3ad2ant1
    @73
    @50
    @75
    simp2
    @73
    @50
    @75
    simp3
    infleinflem1
    3exp
    rexlimdv
    mpd
    3exp
    rexlimdv
    ad4ant14
    mpd
    xrlexaddrp
    syldan
    pm2.61dan
    syldan
    pm2.61dan
end
