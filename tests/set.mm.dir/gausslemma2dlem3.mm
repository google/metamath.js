include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "oveq1.mm"
include "breq1d.mm"
include "oveq2d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "wn.mm"
include "cn.mm"
include "gausslemma2dlem0a.mm"
include "cle.mm"
include "cz.mm"
include "w3a.mm"
include "wi.mm"
include "elfz2.mm"
include "c4.mm"
include "cfl.mm"
include "oveq1i.mm"
include "breq1i.mm"
include "cr.mm"
include "nnre.mm"
include "4re.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "fllelt.mm"
include "syl.mm"
include "flcld.mm"
include "zred.mm"
include "peano2re.mm"
include "zre.mm"
include "adantr.mm"
include "ltleletr.mm"
include "syl3anc.mm"
include "expd.mm"
include "adantld.mm"
include "mpd.mm"
include "imp.mm"
include "wb.mm"
include "rehalfcld.mm"
include "2re.mm"
include "remulcld.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lediv1.mm"
include "cc.mm"
include "nncn.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "2t2e4.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "zcn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divcan4d.mm"
include "breqan12rd.mm"
include "bitrd.mm"
include "mpbird.mm"
include "exp31.mm"
include "com23.mm"
include "syl5bi.mm"
include "3ad2ant3.mm"
include "com12.mm"
include "impcom.mm"
include "sylbi.mm"
include "elfzelz.mm"
include "lenlt.mm"
include "syl2an.mm"
include "mpbid.mm"
include "sylan.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "cn0.mm"
include "gausslemma2dlem0d.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzss1.mm"
include "sselda.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "ralrimiva.mm"

theorem gausslemma2dlem3
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cH: class H
  let cM: class M
  let vy: setvar y
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )
  assume gausslemma2d.m: |- M = ( |_ ` ( P / 4 ) )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint H k
  disjoint R k
  disjoint k ph
  disjoint M x
  disjoint k x
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H l
  disjoint k l
  disjoint R l
  disjoint l ph
  assert |- ( ph -> A. k e. ( ( M + 1 ) ... H ) ( R ` k ) = ( P - ( k x. 2 ) ) )

  proof
    wph
    vk
    cv
    #
    cR
    cfv
    cP
    @0
    c2
    cmul
    co
    #
    cmin
    co
    #
    wceq
    vk
    cM
    c1
    caddc
    co
    #
    cH
    cfz
    co
    #
    wph
    @0
    @4
    wcel
    #
    wa
    #
    vx
    @0
    vx
    cv
    #
    c2
    cmul
    co
    #
    cP
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @8
    cP
    @8
    cmin
    co
    #
    cif
    #
    @2
    c1
    cH
    cfz
    co
    #
    cR
    cvv
    cR
    vx
    @13
    @12
    cmpt
    wceq
    @6
    gausslemma2d.r
    a1i
    @6
    @7
    @0
    wceq
    #
    wa
    #
    @12
    @1
    @9
    clt
    wbr
    #
    @1
    @2
    cif
    #
    @2
    @14
    @12
    @17
    wceq
    @6
    @14
    @10
    @16
    @8
    @11
    @1
    @2
    @14
    @8
    @1
    @9
    clt
    @7
    @0
    c2
    cmul
    oveq1
    #
    breq1d
    @18
    @14
    @8
    @1
    cP
    cmin
    @18
    oveq2d
    ifbieq12d
    adantl
    @15
    @16
    @1
    @2
    @6
    @16
    wn
    #
    @14
    wph
    cP
    cn
    wcel
    #
    @5
    @19
    wph
    cP
    gausslemma2d.p
    gausslemma2dlem0a
    @20
    @5
    wa
    @9
    @1
    cle
    wbr
    #
    @19
    @5
    @20
    @21
    @5
    @3
    cz
    wcel
    #
    cH
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    w3a
    #
    @3
    @0
    cle
    wbr
    #
    @0
    cH
    cle
    wbr
    #
    wa
    #
    wa
    @20
    @21
    wi
    #
    @0
    @3
    cH
    elfz2
    @28
    @25
    @29
    @26
    @25
    @29
    wi
    @27
    @25
    @26
    @29
    @24
    @22
    @26
    @29
    wi
    @23
    @26
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    @0
    cle
    wbr
    #
    @24
    @29
    @3
    @32
    @0
    cle
    cM
    @31
    c1
    caddc
    gausslemma2d.m
    oveq1i
    breq1i
    @24
    @20
    @33
    @21
    @24
    @20
    @33
    @21
    @24
    @20
    wa
    #
    @33
    wa
    @21
    @30
    @0
    cle
    wbr
    #
    @34
    @33
    @35
    @34
    @31
    @30
    cle
    wbr
    #
    @30
    @32
    clt
    wbr
    #
    wa
    #
    @33
    @35
    wi
    #
    @34
    @30
    cr
    wcel
    #
    @38
    @20
    @40
    @24
    @20
    cP
    c4
    cP
    nnre
    #
    c4
    cr
    wcel
    @20
    4re
    a1i
    c4
    cc0
    wne
    @20
    4ne0
    a1i
    redivcld
    #
    adantl
    #
    @30
    fllelt
    syl
    @34
    @37
    @39
    @36
    @34
    @37
    @33
    @35
    @34
    @40
    @32
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @37
    @33
    wa
    @35
    wi
    @43
    @20
    @44
    @24
    @20
    @31
    cr
    wcel
    @44
    @20
    @31
    @20
    @30
    @42
    flcld
    zred
    @31
    peano2re
    syl
    adantl
    @24
    @45
    @20
    @0
    zre
    #
    adantr
    @30
    @32
    @0
    ltleletr
    syl3anc
    expd
    adantld
    mpd
    imp
    @34
    @21
    @35
    wb
    @33
    @34
    @21
    @9
    c2
    cdiv
    co
    #
    @1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @35
    @34
    @9
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @21
    @49
    wb
    @20
    @50
    @24
    @20
    cP
    @41
    rehalfcld
    #
    adantl
    @24
    @51
    @20
    @24
    @0
    c2
    @46
    @52
    @24
    2re
    a1i
    remulcld
    adantr
    @54
    @34
    @52
    @53
    2re
    2pos
    pm3.2i
    a1i
    @9
    @1
    c2
    lediv1
    syl3anc
    @20
    @24
    @47
    @30
    @48
    @0
    cle
    @20
    @47
    cP
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @30
    @20
    cP
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    wa
    #
    @59
    @47
    @57
    wceq
    cP
    nncn
    @59
    @20
    2cnne0
    a1i
    #
    @60
    cP
    c2
    c2
    divdiv1
    syl3anc
    @56
    c4
    cP
    cdiv
    2t2e4
    oveq2i
    syl6eq
    @24
    @0
    c2
    @0
    zcn
    @24
    2cnd
    @58
    @24
    2ne0
    a1i
    divcan4d
    breqan12rd
    bitrd
    adantr
    mpbird
    exp31
    com23
    syl5bi
    3ad2ant3
    com12
    adantr
    impcom
    sylbi
    impcom
    @20
    @50
    @51
    @21
    @19
    wb
    @5
    @55
    @5
    @0
    c2
    @5
    @0
    @0
    @3
    cH
    elfzelz
    zred
    @52
    @5
    2re
    a1i
    remulcld
    @9
    @1
    lenlt
    syl2an
    mpbid
    sylan
    adantr
    iffalsed
    eqtrd
    wph
    @4
    @13
    @0
    wph
    @3
    c1
    cuz
    cfv
    #
    wcel
    #
    @4
    @13
    wss
    wph
    cM
    cn0
    wcel
    #
    @62
    wph
    cP
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2dlem0d
    @63
    @3
    cn
    @61
    cM
    nn0p1nn
    nnuz
    syl6eleq
    syl
    @3
    c1
    cH
    fzss1
    syl
    sselda
    @6
    cP
    @1
    cmin
    ovexd
    fvmptd
    ralrimiva
end
