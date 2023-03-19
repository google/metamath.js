include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "cwwlksn.mm"
include "wi.mm"
include "wa.mm"
include "cwwlks.mm"
include "chash.mm"
include "wb.mm"
include "peano2nn0.mm"
include "iswwlksn.mm"
include "syl.mm"
include "cmin.mm"
include "cvv.mm"
include "cvtx.mm"
include "cword.mm"
include "eqid.mm"
include "wwlkbp.mm"
include "lencl.mm"
include "eqcom.mm"
include "cc.mm"
include "nn0cn.mm"
include "adantr.mm"
include "1cnd.mm"
include "adantl.mm"
include "subadd2.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "syl5bb.mm"
include "biimpi.mm"
include "syl6bi.mm"
include "ex.mm"
include "com23.mm"
include "simpl2im.mm"
include "imp.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "simpll.mm"
include "nn0ge0.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nn0re.mm"
include "addge02d.mm"
include "mpbid.mm"
include "addassd.mm"
include "1p1e2.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "breq2.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "jca.mm"
include "wwlksm1edg.mm"
include "eqeltrd.mm"
include "expcom.mm"
include "sylbid.mm"
include "com12.mm"
include "cfz.mm"
include "cv.mm"
include "cpr.mm"
include "cfzo.mm"
include "wral.mm"
include "wwlknp.mm"
include "peano2re.mm"
include "lep1d.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "oveq2.mm"
include "eleqtrrd.mm"
include "adantll.mm"
include "3adant3.mm"
include "swrd0len.mm"
include "exp31.mm"
include "eleq2s.mm"
include "3imp.mm"
include "wwlksnextproplem1.mm"
include "3adant2.mm"
include "simp2.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"

theorem wwlksnextproplem3
  let vw: setvar w
  let cP: class P
  let cE: class E
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vi: setvar i
  assume wwlksnextprop.x: |- X = ( ( N + 1 ) WWalksN G )
  assume wwlksnextprop.e: |- E = ( Edg ` G )
  assume wwlksnextprop.y: |- Y = { w e. ( N WWalksN G ) | ( w ` 0 ) = P }

  disjoint G w
  disjoint N w
  disjoint P w
  disjoint W w
  disjoint G i
  disjoint E i
  disjoint N i
  disjoint W i
  assert |- ( ( W e. X /\ ( W ` 0 ) = P /\ N e. NN0 ) -> ( W substr <. 0 , ( N + 1 ) >. ) e. Y )

  proof
    cW
    cX
    wcel
    #
    cc0
    cW
    cfv
    #
    cP
    wceq
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cW
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @7
    cfv
    #
    cP
    wceq
    #
    @7
    cY
    wcel
    @0
    @2
    @3
    @9
    @2
    @3
    @9
    wi
    wi
    cW
    @5
    cG
    cwwlksn
    co
    #
    cX
    cW
    @12
    wcel
    #
    @2
    @3
    @9
    @13
    @2
    wa
    #
    @3
    wa
    #
    @9
    @7
    cG
    cwwlks
    cfv
    #
    wcel
    #
    @7
    chash
    cfv
    @5
    wceq
    #
    wa
    #
    @15
    @17
    @18
    @14
    @3
    @17
    @13
    @3
    @17
    wi
    @2
    @3
    @13
    @17
    @3
    @13
    cW
    @16
    wcel
    #
    cW
    chash
    cfv
    #
    @5
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @17
    @3
    @5
    cn0
    wcel
    #
    @13
    @24
    wb
    cN
    peano2nn0
    #
    cG
    @5
    cW
    iswwlksn
    syl
    @24
    @3
    @17
    @24
    @3
    wa
    #
    @7
    cW
    cc0
    @21
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @16
    @27
    @6
    @29
    cW
    csubstr
    @27
    @5
    @28
    cc0
    @24
    @3
    @5
    @28
    wceq
    #
    @20
    @23
    @3
    @31
    wi
    #
    @20
    cG
    cvv
    wcel
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @23
    @32
    wi
    #
    cG
    @33
    cW
    @33
    eqid
    #
    wwlkbp
    @34
    @21
    cn0
    wcel
    #
    @35
    @33
    cW
    lencl
    @37
    @3
    @23
    @31
    @37
    @3
    @23
    @31
    wi
    @37
    @3
    wa
    #
    @23
    @28
    @5
    wceq
    #
    @31
    @23
    @22
    @21
    wceq
    #
    @38
    @39
    @21
    @22
    eqcom
    @38
    @21
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @40
    @39
    wb
    @37
    @41
    @3
    @21
    nn0cn
    adantr
    @38
    1cnd
    @3
    @43
    @37
    @3
    @25
    @43
    @26
    @5
    nn0cn
    syl
    adantl
    @41
    @42
    @43
    w3a
    @39
    @40
    @21
    c1
    @5
    subadd2
    bicomd
    syl3anc
    syl5bb
    @39
    @31
    @28
    @5
    eqcom
    biimpi
    syl6bi
    ex
    com23
    syl
    simpl2im
    imp
    imp
    opeq2d
    oveq2d
    @27
    @20
    c2
    @21
    cle
    wbr
    #
    wa
    @30
    @16
    wcel
    @27
    @20
    @44
    @20
    @23
    @3
    simpll
    @27
    @44
    c2
    @22
    cle
    wbr
    #
    @3
    @45
    @24
    @3
    c2
    cN
    c2
    caddc
    co
    #
    @22
    cle
    @3
    cc0
    cN
    cle
    wbr
    c2
    @46
    cle
    wbr
    cN
    nn0ge0
    @3
    c2
    cN
    c2
    cr
    wcel
    @3
    2re
    a1i
    cN
    nn0re
    #
    addge02d
    mpbid
    @3
    @22
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @46
    @3
    cN
    c1
    c1
    cN
    nn0cn
    @3
    1cnd
    #
    @49
    addassd
    @3
    @48
    c2
    cN
    caddc
    @48
    c2
    wceq
    @3
    1p1e2
    a1i
    oveq2d
    eqtrd
    breqtrrd
    adantl
    @23
    @44
    @45
    wb
    @20
    @3
    @21
    @22
    c2
    cle
    breq2
    ad2antlr
    mpbird
    jca
    cG
    cW
    wwlksm1edg
    syl
    eqeltrd
    expcom
    sylbid
    com12
    adantr
    imp
    @15
    @34
    @5
    cc0
    @21
    cfz
    co
    #
    wcel
    #
    wa
    #
    @18
    @14
    @3
    @52
    @13
    @3
    @52
    wi
    #
    @2
    @13
    @34
    @23
    vi
    cv
    #
    cW
    cfv
    @54
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @5
    cfzo
    co
    wral
    #
    w3a
    @53
    vi
    cE
    cG
    @5
    @33
    cW
    @36
    wwlksnextprop.e
    wwlknp
    @34
    @23
    @53
    @55
    @34
    @23
    wa
    #
    @3
    @52
    @56
    @3
    wa
    @34
    @51
    @34
    @23
    @3
    simpll
    @23
    @3
    @51
    @34
    @23
    @3
    wa
    @5
    cc0
    @22
    cfz
    co
    #
    @50
    @3
    @5
    @57
    wcel
    #
    @23
    @3
    @25
    @22
    cn0
    wcel
    #
    @5
    @22
    cle
    wbr
    @58
    @26
    @3
    @25
    @59
    @26
    @5
    peano2nn0
    syl
    @3
    @5
    @3
    cN
    cr
    wcel
    @5
    cr
    wcel
    @47
    cN
    peano2re
    syl
    lep1d
    @5
    @22
    elfz2nn0
    syl3anbrc
    adantl
    @23
    @50
    @57
    wceq
    @3
    @21
    @22
    cc0
    cfz
    oveq2
    adantr
    eleqtrrd
    adantll
    jca
    ex
    3adant3
    syl
    adantr
    imp
    @33
    cW
    @5
    swrd0len
    syl
    jca
    @3
    @9
    @19
    wb
    @14
    cG
    cN
    @7
    iswwlksn
    adantl
    mpbird
    exp31
    wwlksnextprop.x
    eleq2s
    3imp
    @4
    @10
    @1
    cP
    @0
    @3
    @10
    @1
    wceq
    @2
    cG
    cN
    cW
    cX
    wwlksnextprop.x
    wwlksnextproplem1
    3adant2
    @0
    @2
    @3
    simp2
    eqtrd
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    @11
    vw
    @7
    @8
    cY
    @60
    @7
    wceq
    @61
    @10
    cP
    cc0
    @60
    @7
    fveq1
    eqeq1d
    wwlksnextprop.y
    elrab2
    sylanbrc
end
