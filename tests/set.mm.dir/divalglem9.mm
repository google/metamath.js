include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wreu.mm"
include "wrex.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "cr.mm"
include "cinf.mm"
include "divalglem2.mm"
include "eqeltri.mm"
include "cc0.mm"
include "cle.mm"
include "divalglem5.mm"
include "simpri.mm"
include "breq1.mm"
include "rspcev.mm"
include "mp2an.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cz.mm"
include "cdvds.mm"
include "cn0.mm"
include "oveq2.mm"
include "breq2d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "nn0zd.mm"
include "zsubcl.mm"
include "mpan.mm"
include "anim12i.mm"
include "syl2an.mm"
include "simprbi.mm"
include "dvds2sub.mm"
include "mp3an1.mm"
include "sylc.mm"
include "cc.mm"
include "zcn.mm"
include "caddc.mm"
include "zrei.mm"
include "recni.mm"
include "subidi.mm"
include "oveq1i.mm"
include "0cn.mm"
include "subsub2.mm"
include "syl5eq.mm"
include "sub4.mm"
include "mpanl12.mm"
include "subcl.mm"
include "ancoms.mm"
include "addid2d.mm"
include "3eqtr3d.mm"
include "mpbid.mm"
include "wb.mm"
include "absdvdsb.mm"
include "sylancr.mm"
include "wne.mm"
include "cn.mm"
include "nnabscl.mm"
include "nnzi.mm"
include "divides.mm"
include "adantr.mm"
include "divalglem8.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ex.mm"
include "rgen2a.mm"
include "reu4.mm"
include "mpbir2an.mm"

theorem divalglem9
  let vx: setvar x
  let cD: class D
  let cR: class R
  let cS: class S
  let cN: class N
  let vr: setvar r
  let vk: setvar k
  let vy: setvar y
  let vq: setvar q
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume divalglem8.1: |- N e. ZZ
  assume divalglem8.2: |- D e. ZZ
  assume divalglem8.3: |- D =/= 0
  assume divalglem8.4: |- S = { r e. NN0 | D || ( N - r ) }
  assume divalglem9.5: |- R = inf ( S , RR , < )

  disjoint D r
  disjoint D x
  disjoint r x
  disjoint R x
  disjoint S x
  disjoint D r
  disjoint D x
  disjoint r x
  disjoint N r
  disjoint N x
  disjoint S x
  disjoint D k
  disjoint D y
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint r y
  disjoint x y
  disjoint S k
  disjoint S y
  disjoint D q
  disjoint D z
  disjoint q r
  disjoint q x
  disjoint q z
  disjoint r z
  disjoint x z
  disjoint N q
  disjoint N z
  disjoint S z
  disjoint X z
  disjoint Y z
  assert |- E! x e. S x < ( abs ` D )

  proof
    vx
    cv
    #
    cD
    cabs
    cfv
    #
    clt
    wbr
    #
    vx
    cS
    wreu
    @2
    vx
    cS
    wrex
    #
    @2
    vy
    cv
    #
    @1
    clt
    wbr
    #
    wa
    #
    @0
    @4
    wceq
    #
    wi
    #
    vy
    cS
    wral
    vx
    cS
    wral
    cR
    cS
    wcel
    cR
    @1
    clt
    wbr
    #
    @3
    cR
    cS
    cr
    clt
    cinf
    cS
    divalglem9.5
    cD
    cS
    cN
    vr
    divalglem8.1
    divalglem8.2
    divalglem8.3
    divalglem8.4
    divalglem2
    eqeltri
    cc0
    cR
    cle
    wbr
    @9
    cD
    cR
    cS
    cN
    vr
    divalglem8.1
    divalglem8.2
    divalglem8.3
    divalglem8.4
    divalglem9.5
    divalglem5
    simpri
    @2
    @9
    vx
    cR
    cS
    @0
    cR
    @1
    clt
    breq1
    rspcev
    mp2an
    @8
    vx
    vy
    cS
    @0
    cS
    wcel
    #
    @4
    cS
    wcel
    #
    wa
    #
    @6
    @7
    @12
    @6
    wa
    #
    vk
    cv
    #
    @1
    cmul
    co
    @4
    @0
    cmin
    co
    #
    wceq
    #
    vk
    cz
    wrex
    #
    @7
    @12
    @17
    @6
    @12
    @1
    @15
    cdvds
    wbr
    #
    @17
    @12
    cD
    @15
    cdvds
    wbr
    #
    @18
    @12
    cD
    cN
    @0
    cmin
    co
    #
    cN
    @4
    cmin
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    @19
    @12
    @20
    cz
    wcel
    #
    @21
    cz
    wcel
    #
    wa
    #
    cD
    @20
    cdvds
    wbr
    #
    cD
    @21
    cdvds
    wbr
    #
    wa
    #
    @23
    @10
    @0
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @26
    @11
    @10
    @0
    @10
    @0
    cn0
    wcel
    #
    @27
    cD
    cN
    vr
    cv
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    @27
    vr
    @0
    cn0
    cS
    @33
    @0
    wceq
    @34
    @20
    cD
    cdvds
    @33
    @0
    cN
    cmin
    oveq2
    breq2d
    divalglem8.4
    elrab2
    #
    simplbi
    nn0zd
    #
    @11
    @4
    @11
    @4
    cn0
    wcel
    #
    @28
    @35
    @28
    vr
    @4
    cn0
    cS
    @33
    @4
    wceq
    @34
    @21
    cD
    cdvds
    @33
    @4
    cN
    cmin
    oveq2
    breq2d
    divalglem8.4
    elrab2
    #
    simplbi
    nn0zd
    #
    @30
    @24
    @31
    @25
    cN
    cz
    wcel
    #
    @30
    @24
    divalglem8.1
    cN
    @0
    zsubcl
    mpan
    @41
    @31
    @25
    divalglem8.1
    cN
    @4
    zsubcl
    mpan
    anim12i
    syl2an
    @10
    @27
    @11
    @28
    @10
    @32
    @27
    @36
    simprbi
    @11
    @38
    @28
    @39
    simprbi
    anim12i
    cD
    cz
    wcel
    #
    @24
    @25
    @29
    @23
    wi
    divalglem8.2
    cD
    @20
    @21
    dvds2sub
    mp3an1
    sylc
    @12
    @22
    @15
    cD
    cdvds
    @10
    @30
    @31
    @22
    @15
    wceq
    #
    @11
    @37
    @40
    @30
    @0
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @43
    @31
    @0
    zcn
    @4
    zcn
    @44
    @45
    wa
    #
    cN
    cN
    cmin
    co
    #
    @0
    @4
    cmin
    co
    #
    cmin
    co
    #
    cc0
    @15
    caddc
    co
    #
    @22
    @15
    @46
    @49
    cc0
    @48
    cmin
    co
    #
    @50
    @47
    cc0
    @48
    cmin
    cN
    cN
    cN
    divalglem8.1
    zrei
    recni
    #
    subidi
    oveq1i
    cc0
    cc
    wcel
    @44
    @45
    @51
    @50
    wceq
    0cn
    cc0
    @0
    @4
    subsub2
    mp3an1
    syl5eq
    cN
    cc
    wcel
    #
    @53
    @46
    @49
    @22
    wceq
    @52
    @52
    cN
    cN
    @0
    @4
    sub4
    mpanl12
    @46
    @15
    @45
    @44
    @15
    cc
    wcel
    @4
    @0
    subcl
    ancoms
    addid2d
    3eqtr3d
    syl2an
    syl2an
    breq2d
    mpbid
    @10
    @30
    @31
    @19
    @18
    wb
    #
    @11
    @37
    @40
    @30
    @31
    wa
    #
    @42
    @15
    cz
    wcel
    #
    @54
    divalglem8.2
    @31
    @30
    @56
    @4
    @0
    zsubcl
    ancoms
    #
    cD
    @15
    absdvdsb
    sylancr
    syl2an
    mpbid
    @10
    @30
    @31
    @18
    @17
    wb
    #
    @11
    @37
    @40
    @55
    @1
    cz
    wcel
    @56
    @58
    @1
    @42
    cD
    cc0
    wne
    @1
    cn
    wcel
    divalglem8.2
    divalglem8.3
    cD
    nnabscl
    mp2an
    nnzi
    @57
    vk
    @1
    @15
    divides
    sylancr
    syl2an
    mpbid
    adantr
    @13
    @16
    @7
    vk
    cz
    cD
    cS
    @14
    cN
    @0
    @4
    vr
    divalglem8.1
    divalglem8.2
    divalglem8.3
    divalglem8.4
    divalglem8
    rexlimdv
    mpd
    ex
    rgen2a
    @2
    @5
    vx
    vy
    cS
    @0
    @4
    @1
    clt
    breq1
    reu4
    mpbir2an
end
