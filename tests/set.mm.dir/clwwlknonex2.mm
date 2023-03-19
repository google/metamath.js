include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cpr.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cclwwlknon.mm"
include "cs1.mm"
include "cconcat.mm"
include "cclwwlkn.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wne.mm"
include "wb.mm"
include "uz3m2nn.mm"
include "nnne0d.mm"
include "3ad2ant3.mm"
include "clwwlknonel.mm"
include "syl.mm"
include "simpr11.mm"
include "adantr.mm"
include "simpll1.mm"
include "simpll2.mm"
include "ccatw2s1cl.mm"
include "syl3anc.mm"
include "cun.mm"
include "clwwlknonex2lem2.mm"
include "simp11.mm"
include "ad2antlr.mm"
include "ccatw2s1len.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "simp3.mm"
include "simp2.mm"
include "anim12i.mm"
include "clwwlknonex2lem1.mm"
include "eqtrd.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "ccatws1cl.mm"
include "lswccats1.mm"
include "stoic3.mm"
include "clt.mm"
include "wbr.mm"
include "nngt0d.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "3ad2ant2.mm"
include "com12.mm"
include "imp.mm"
include "ccat2s1fst.mm"
include "syl22anc.mm"
include "preq12d.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "preq2.mm"
include "eleq1d.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "3ad2ant1.mm"
include "oveq1.mm"
include "cc.mm"
include "eluzelcn.mm"
include "2cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "sylan9eq.mm"
include "ex.mm"
include "jca.mm"
include "exp31.mm"
include "sylbid.mm"
include "com23.mm"
include "3imp.mm"
include "cn.mm"
include "eluzge3nn.mm"
include "isclwwlknx.mm"

theorem clwwlknonex2
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vi: setvar i
  assume clwwlknonex2.v: |- V = ( Vtx ` G )
  assume clwwlknonex2.e: |- E = ( Edg ` G )


  assert |- ( ( ( X e. V /\ Y e. V /\ N e. ( ZZ>= ` 3 ) ) /\ { X , Y } e. E /\ W e. ( X ( ClWWalksNOn ` G ) ( N - 2 ) ) ) -> ( ( W ++ <" X "> ) ++ <" Y "> ) e. ( N ClWWalksN G ) )

  proof
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    cX
    cY
    cpr
    #
    cE
    wcel
    #
    cW
    cX
    cN
    c2
    cmin
    co
    #
    cG
    cclwwlknon
    cfv
    co
    wcel
    #
    w3a
    cW
    cX
    cs1
    cconcat
    co
    #
    cY
    cs1
    cconcat
    co
    #
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    @9
    cV
    cword
    #
    wcel
    #
    vi
    cv
    #
    @9
    cfv
    @13
    c1
    caddc
    co
    #
    @9
    cfv
    cpr
    cE
    wcel
    #
    vi
    cc0
    @9
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @9
    clsw
    cfv
    #
    cc0
    @9
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @16
    cN
    wceq
    #
    wa
    #
    @3
    @5
    @7
    @26
    @3
    @7
    @5
    @26
    @3
    @7
    cW
    @11
    wcel
    #
    @13
    cW
    cfv
    @14
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cW
    clsw
    cfv
    cc0
    cW
    cfv
    #
    cpr
    cE
    wcel
    #
    w3a
    #
    @28
    @6
    wceq
    #
    @32
    cX
    wceq
    #
    w3a
    #
    @5
    @26
    wi
    @3
    @6
    cc0
    wne
    #
    @7
    @37
    wb
    @2
    @0
    @38
    @1
    @2
    @6
    cN
    uz3m2nn
    #
    nnne0d
    3ad2ant3
    vi
    cE
    cG
    @6
    cV
    cW
    cX
    clwwlknonex2.v
    clwwlknonex2.e
    clwwlknonel
    syl
    @3
    @37
    @5
    @26
    @3
    @37
    wa
    #
    @5
    wa
    #
    @24
    @25
    @41
    @12
    @19
    @23
    @41
    @27
    @0
    @1
    @12
    @40
    @27
    @5
    @27
    @31
    @33
    @35
    @36
    @3
    simpr11
    adantr
    @0
    @1
    @2
    @37
    @5
    simpll1
    #
    @0
    @1
    @2
    @37
    @5
    simpll2
    #
    cV
    cW
    cX
    cY
    ccatw2s1cl
    syl3anc
    @41
    @19
    @15
    vi
    @30
    @29
    @28
    cpr
    cun
    #
    wral
    vi
    cE
    cG
    cN
    cV
    cW
    cX
    cY
    clwwlknonex2.v
    clwwlknonex2.e
    clwwlknonex2lem2
    @41
    @15
    vi
    @18
    @44
    @41
    @18
    cc0
    @28
    c2
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    @44
    @41
    @17
    @46
    cc0
    cfzo
    @41
    @16
    @45
    c1
    cmin
    @41
    @27
    @16
    @45
    wceq
    #
    @37
    @27
    @3
    @5
    @27
    @31
    @33
    @35
    @36
    simp11
    ad2antlr
    #
    cV
    cW
    cX
    cY
    ccatw2s1len
    #
    syl
    oveq1d
    oveq2d
    @41
    @2
    @35
    wa
    #
    @47
    @44
    wceq
    @40
    @51
    @5
    @3
    @2
    @37
    @35
    @0
    @1
    @2
    simp3
    @34
    @35
    @36
    simp2
    anim12i
    adantr
    cN
    cW
    clwwlknonex2lem1
    syl
    eqtrd
    raleqdv
    mpbird
    @41
    @22
    cY
    @32
    cpr
    #
    cE
    @41
    @20
    cY
    @21
    @32
    @41
    @27
    @0
    @1
    @20
    cY
    wceq
    #
    @49
    @42
    @43
    @27
    @0
    @8
    @11
    wcel
    @1
    @53
    cV
    cW
    cX
    ccatws1cl
    cY
    cV
    @8
    lswccats1
    stoic3
    syl3anc
    @41
    @27
    cc0
    @28
    clt
    wbr
    #
    @0
    @1
    @21
    @32
    wceq
    @49
    @40
    @54
    @5
    @3
    @37
    @54
    @2
    @0
    @37
    @54
    wi
    @1
    @37
    @2
    @54
    @35
    @34
    @2
    @54
    wi
    @36
    @2
    @54
    @35
    cc0
    @6
    clt
    wbr
    @2
    @6
    @39
    nngt0d
    @28
    @6
    cc0
    clt
    breq2
    syl5ibr
    3ad2ant2
    com12
    3ad2ant3
    imp
    adantr
    @42
    @43
    cV
    cW
    cX
    cY
    ccat2s1fst
    syl22anc
    preq12d
    @41
    @52
    cE
    wcel
    #
    cY
    cX
    cpr
    #
    cE
    wcel
    #
    @5
    @57
    @40
    @5
    @57
    @4
    @56
    cE
    cX
    cY
    prcom
    eleq1i
    biimpi
    adantl
    @37
    @55
    @57
    wb
    #
    @3
    @5
    @36
    @34
    @58
    @35
    @36
    @52
    @56
    cE
    @32
    cX
    cY
    preq2
    eleq1d
    3ad2ant3
    ad2antlr
    mpbird
    eqeltrd
    3jca
    @41
    @16
    @45
    cN
    @37
    @48
    @3
    @5
    @34
    @35
    @48
    @36
    @27
    @31
    @48
    @33
    @50
    3ad2ant1
    3ad2ant1
    ad2antlr
    @40
    @45
    cN
    wceq
    #
    @5
    @3
    @37
    @59
    @2
    @0
    @37
    @59
    wi
    @1
    @37
    @2
    @59
    @35
    @34
    @2
    @59
    wi
    @36
    @35
    @2
    @59
    @35
    @2
    @45
    @6
    c2
    caddc
    co
    #
    cN
    @28
    @6
    c2
    caddc
    oveq1
    @2
    cN
    cc
    wcel
    c2
    cc
    wcel
    @60
    cN
    wceq
    c3
    cN
    eluzelcn
    2cn
    cN
    c2
    npcan
    sylancl
    sylan9eq
    ex
    3ad2ant2
    com12
    3ad2ant3
    imp
    adantr
    eqtrd
    jca
    exp31
    sylbid
    com23
    3imp
    @3
    @5
    @10
    @26
    wb
    #
    @7
    @2
    @0
    @61
    @1
    @2
    cN
    cn
    wcel
    @61
    cN
    eluzge3nn
    vi
    cE
    cG
    cN
    cV
    @9
    clwwlknonex2.v
    clwwlknonex2.e
    isclwwlknx
    syl
    3ad2ant3
    3ad2ant1
    mpbird
end
