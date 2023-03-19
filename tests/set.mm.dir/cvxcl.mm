include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "ralrimivva.mm"
include "ad2antrr.mm"
include "wi.mm"
include "simpr1.mm"
include "simpr2.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mpd.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cr.mm"
include "unitssre.mm"
include "simpr3.mm"
include "sseldi.mm"
include "recnd.mm"
include "nncan.mm"
include "sylancr.mm"
include "oveq1d.mm"
include "sseldd.mm"
include "simpr.mm"
include "simplr3.mm"
include "iirev.mm"
include "syl.mm"
include "lincmb01cmp.mm"
include "syl31anc.mm"
include "eqeltrrd.mm"
include "pncan3.mm"
include "sylancl.mm"
include "1re.mm"
include "resubcl.mm"
include "adddird.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "sylan9eqr.mm"
include "eqeltrd.mm"
include "mulcld.mm"
include "addcomd.mm"
include "lttri4d.mm"
include "mpjao3dan.mm"

theorem cvxcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cT: class T
  let cX: class X
  let cY: class Y
  assume cvxcl.1: |- ( ph -> D C_ RR )
  assume cvxcl.2: |- ( ( ph /\ ( x e. D /\ y e. D ) ) -> ( x [,] y ) C_ D )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( ph /\ ( X e. D /\ Y e. D /\ T e. ( 0 [,] 1 ) ) ) -> ( ( T x. X ) + ( ( 1 - T ) x. Y ) ) e. D )

  proof
    wph
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    cT
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cY
    clt
    wbr
    #
    cT
    cX
    cmul
    co
    #
    c1
    cT
    cmin
    co
    #
    cY
    cmul
    co
    #
    caddc
    co
    #
    cD
    wcel
    cX
    cY
    wceq
    #
    cY
    cX
    clt
    wbr
    #
    @5
    @6
    wa
    #
    cX
    cY
    cicc
    co
    #
    cD
    @10
    @13
    vx
    cv
    #
    vy
    cv
    #
    cicc
    co
    #
    cD
    wss
    #
    vy
    cD
    wral
    vx
    cD
    wral
    #
    @14
    cD
    wss
    #
    wph
    @19
    @4
    @6
    wph
    @18
    vx
    vy
    cD
    cD
    cvxcl.2
    ralrimivva
    #
    ad2antrr
    @5
    @19
    @20
    wi
    #
    @6
    @5
    @0
    @1
    @22
    wph
    @0
    @1
    @3
    simpr1
    #
    wph
    @0
    @1
    @3
    simpr2
    #
    @18
    @20
    cX
    @16
    cicc
    co
    #
    cD
    wss
    vx
    vy
    cX
    cY
    cD
    cD
    @15
    cX
    wceq
    @17
    @25
    cD
    @15
    cX
    @16
    cicc
    oveq1
    sseq1d
    @16
    cY
    wceq
    @25
    @14
    cD
    @16
    cY
    cX
    cicc
    oveq2
    sseq1d
    rspc2v
    syl2anc
    adantr
    mpd
    @13
    c1
    @8
    cmin
    co
    #
    cX
    cmul
    co
    #
    @9
    caddc
    co
    #
    @10
    @14
    @5
    @28
    @10
    wceq
    @6
    @5
    @27
    @7
    @9
    caddc
    @5
    @26
    cT
    cX
    cmul
    @5
    c1
    cc
    wcel
    #
    cT
    cc
    wcel
    #
    @26
    cT
    wceq
    ax-1cn
    @5
    cT
    @5
    @2
    cr
    cT
    unitssre
    wph
    @0
    @1
    @3
    simpr3
    sseldi
    #
    recnd
    #
    c1
    cT
    nncan
    sylancr
    oveq1d
    oveq1d
    adantr
    @13
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @6
    @8
    @2
    wcel
    #
    @28
    @14
    wcel
    @5
    @33
    @6
    @5
    cD
    cr
    cX
    wph
    cD
    cr
    wss
    @4
    cvxcl.1
    adantr
    #
    @23
    sseldd
    #
    adantr
    @5
    @34
    @6
    @5
    cD
    cr
    cY
    @36
    @24
    sseldd
    #
    adantr
    @5
    @6
    simpr
    @13
    @3
    @35
    @0
    @1
    @3
    wph
    @6
    simplr3
    cT
    iirev
    syl
    cX
    cY
    @8
    lincmb01cmp
    syl31anc
    eqeltrrd
    sseldd
    @5
    @11
    wa
    @10
    cY
    cD
    @11
    @5
    @10
    cT
    cY
    cmul
    co
    #
    @9
    caddc
    co
    #
    cY
    @11
    @7
    @39
    @9
    caddc
    cX
    cY
    cT
    cmul
    oveq2
    oveq1d
    @5
    cT
    @8
    caddc
    co
    #
    cY
    cmul
    co
    c1
    cY
    cmul
    co
    @40
    cY
    @5
    @41
    c1
    cY
    cmul
    @5
    @30
    @29
    @41
    c1
    wceq
    @32
    ax-1cn
    cT
    c1
    pncan3
    sylancl
    oveq1d
    @5
    cT
    @8
    cY
    @32
    @5
    @8
    @5
    c1
    cr
    wcel
    cT
    cr
    wcel
    @8
    cr
    wcel
    1re
    @31
    c1
    cT
    resubcl
    sylancr
    recnd
    #
    @5
    cY
    @38
    recnd
    #
    adddird
    @5
    cY
    @43
    mulid2d
    3eqtr3d
    sylan9eqr
    @5
    @1
    @11
    @24
    adantr
    eqeltrd
    @5
    @12
    wa
    #
    cY
    cX
    cicc
    co
    #
    cD
    @10
    @44
    @19
    @45
    cD
    wss
    #
    wph
    @19
    @4
    @12
    @21
    ad2antrr
    @5
    @19
    @46
    wi
    #
    @12
    @5
    @1
    @0
    @47
    @24
    @23
    @18
    @46
    cY
    @16
    cicc
    co
    #
    cD
    wss
    vx
    vy
    cY
    cX
    cD
    cD
    @15
    cY
    wceq
    @17
    @48
    cD
    @15
    cY
    @16
    cicc
    oveq1
    sseq1d
    @16
    cX
    wceq
    @48
    @45
    cD
    @16
    cX
    cY
    cicc
    oveq2
    sseq1d
    rspc2v
    syl2anc
    adantr
    mpd
    @44
    @10
    @9
    @7
    caddc
    co
    #
    @45
    @5
    @10
    @49
    wceq
    @12
    @5
    @7
    @9
    @5
    cT
    cX
    @32
    @5
    cX
    @37
    recnd
    mulcld
    @5
    @8
    cY
    @42
    @43
    mulcld
    addcomd
    adantr
    @44
    @34
    @33
    @12
    @3
    @49
    @45
    wcel
    @5
    @34
    @12
    @38
    adantr
    @5
    @33
    @12
    @37
    adantr
    @5
    @12
    simpr
    @0
    @1
    @3
    wph
    @12
    simplr3
    cY
    cX
    cT
    lincmb01cmp
    syl31anc
    eqeltrd
    sseldd
    @5
    cX
    cY
    @37
    @38
    lttri4d
    mpjao3dan
end
