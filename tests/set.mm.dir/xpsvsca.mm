include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cmpt2.mm"
include "cfv.mm"
include "cprds.mm"
include "cvsca.mm"
include "cop.mm"
include "wcel.mm"
include "crn.mm"
include "wceq.mm"
include "df-ov.mm"
include "eqid.mm"
include "xpsfval.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "cxp.mm"
include "opelxpi.mm"
include "wf1o.mm"
include "wf.mm"
include "xpsff1o2.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "cvv.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wfo.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "f1ofo.mm"
include "ovexd.mm"
include "csca.mm"
include "wtru.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ovex.mm"
include "cnvex.mm"
include "prdssca.mm"
include "trud.mm"
include "f1ovscpbl.mm"
include "imasvscaval.mm"
include "mpd3an23.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "sylancr.mm"
include "mpd.mm"
include "oveq2d.mm"
include "c2o.mm"
include "cmpt.mm"
include "wa.mm"
include "c0.mm"
include "cif.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61i.mm"
include "adantr.mm"
include "simpr.mm"
include "xpscfv.mm"
include "syl3anc.mm"
include "3eqtr4a.mm"
include "mpteq2dva.mm"
include "cbs.mm"
include "con0.mm"
include "2on.mm"
include "wfn.mm"
include "xpscfn.mm"
include "eleqtrd.mm"
include "prdsvscaval.mm"
include "dffn5.mm"
include "sylib.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem xpsvsca
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vc: setvar c
  let vb: setvar b
  assume xpssca.t: |- T = ( R Xs. S )
  assume xpssca.g: |- G = ( Scalar ` R )
  assume xpssca.1: |- ( ph -> R e. V )
  assume xpssca.2: |- ( ph -> S e. W )
  assume xpsvsca.x: |- X = ( Base ` R )
  assume xpsvsca.y: |- Y = ( Base ` S )
  assume xpsvsca.k: |- K = ( Base ` G )
  assume xpsvsca.m: |- .x. = ( .s ` R )
  assume xpsvsca.n: |- .X. = ( .s ` S )
  assume xpsvsca.p: |- .xb = ( .s ` T )
  assume xpsvsca.3: |- ( ph -> A e. K )
  assume xpsvsca.4: |- ( ph -> B e. X )
  assume xpsvsca.5: |- ( ph -> C e. Y )
  assume xpsvsca.6: |- ( ph -> ( A .x. B ) e. X )
  assume xpsvsca.7: |- ( ph -> ( A .X. C ) e. Y )


  assert |- ( ph -> ( A .xb <. B , C >. ) = <. ( A .x. B ) , ( A .X. C ) >. )

  proof
    wph
    cA
    cB
    csn
    cC
    csn
    ccda
    co
    ccnv
    #
    vx
    vy
    cX
    cY
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    ccnv
    #
    cfv
    #
    c.xb
    co
    #
    cA
    @0
    cG
    cR
    csn
    #
    cS
    csn
    #
    ccda
    co
    #
    ccnv
    #
    cprds
    co
    #
    cvsca
    cfv
    #
    co
    #
    @2
    cfv
    #
    cA
    cB
    cC
    cop
    #
    c.xb
    co
    cA
    cB
    c.x
    co
    #
    cA
    cC
    c.xp
    co
    #
    cop
    #
    wph
    cA
    cK
    wcel
    @0
    @1
    crn
    #
    wcel
    @4
    @12
    wceq
    xpsvsca.3
    wph
    @13
    @1
    cfv
    #
    @0
    @17
    wph
    @18
    cB
    cC
    @1
    co
    #
    @0
    cB
    cC
    @1
    df-ov
    wph
    cB
    cX
    wcel
    #
    cC
    cY
    wcel
    #
    @19
    @0
    wceq
    xpsvsca.4
    xpsvsca.5
    vx
    vy
    cX
    cY
    @1
    cB
    cC
    @1
    eqid
    #
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @13
    cX
    cY
    cxp
    #
    wcel
    #
    @18
    @17
    wcel
    wph
    @20
    @21
    @25
    xpsvsca.4
    xpsvsca.5
    cB
    cC
    cX
    cY
    opelxpi
    syl2anc
    #
    @24
    @17
    @13
    @1
    @24
    @17
    @1
    wf1o
    #
    @24
    @17
    @1
    wf
    vx
    vy
    cX
    cY
    @1
    @22
    xpsff1o2
    #
    @24
    @17
    @1
    f1of
    ax-mp
    ffvelrni
    syl
    eqeltrrd
    #
    wph
    @24
    @9
    c.xb
    @10
    cT
    @2
    cG
    cK
    @17
    cA
    @0
    cvv
    vc
    va
    vb
    wph
    vx
    vy
    cR
    cS
    cT
    @9
    @1
    cG
    cV
    cW
    cX
    cY
    xpssca.t
    xpsvsca.x
    xpsvsca.y
    xpssca.1
    xpssca.2
    @22
    xpssca.g
    @9
    eqid
    #
    xpsval
    wph
    vx
    vy
    cR
    cS
    cT
    @9
    @1
    cG
    cV
    cW
    cX
    cY
    xpssca.t
    xpsvsca.x
    xpsvsca.y
    xpssca.1
    xpssca.2
    @22
    xpssca.g
    @30
    xpslem
    #
    wph
    @17
    @24
    @2
    wf1o
    #
    @17
    @24
    @2
    wfo
    @27
    @32
    wph
    @28
    @24
    @17
    @1
    f1ocnv
    mp1i
    #
    @17
    @24
    @2
    f1ofo
    syl
    wph
    cG
    @8
    cprds
    ovexd
    cG
    @9
    csca
    cfv
    wceq
    wtru
    @9
    @8
    cG
    cvv
    cvv
    @30
    cG
    cvv
    wcel
    #
    wtru
    cG
    cR
    csca
    cfv
    cvv
    xpssca.g
    cR
    csca
    fvex
    eqeltri
    #
    a1i
    @8
    cvv
    wcel
    wtru
    @7
    @5
    @6
    ccda
    ovex
    cnvex
    a1i
    prdssca
    trud
    xpsvsca.k
    @10
    eqid
    #
    xpsvsca.p
    wph
    va
    cv
    vb
    cv
    vc
    cv
    @10
    @2
    cK
    @17
    @24
    @33
    f1ovscpbl
    imasvscaval
    mpd3an23
    wph
    @3
    @13
    cA
    c.xb
    wph
    @18
    @0
    wceq
    #
    @3
    @13
    wceq
    #
    @23
    wph
    @27
    @25
    @37
    @38
    wi
    @28
    @26
    @24
    @17
    @13
    @0
    @1
    f1ocnvfv
    sylancr
    mpd
    oveq2d
    wph
    @12
    @14
    csn
    @15
    csn
    ccda
    co
    ccnv
    #
    @2
    cfv
    #
    @16
    wph
    @11
    @39
    @2
    wph
    vk
    c2o
    cA
    vk
    cv
    #
    @0
    cfv
    #
    @41
    @8
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cmpt
    vk
    c2o
    @41
    @39
    cfv
    #
    cmpt
    #
    @11
    @39
    wph
    vk
    c2o
    @45
    @46
    wph
    @41
    c2o
    wcel
    #
    wa
    #
    cA
    @41
    c0
    wceq
    #
    cB
    cC
    cif
    #
    @50
    cR
    cS
    cif
    #
    cvsca
    cfv
    #
    co
    #
    @50
    @14
    @15
    cif
    #
    @45
    @46
    @50
    @54
    @55
    wceq
    @50
    @54
    @14
    @55
    @50
    cA
    cA
    @51
    cB
    @53
    c.x
    @50
    @53
    cR
    cvsca
    cfv
    c.x
    @50
    @52
    cR
    cvsca
    @50
    cR
    cS
    iftrue
    fveq2d
    xpsvsca.m
    syl6eqr
    @50
    cA
    eqidd
    @50
    cB
    cC
    iftrue
    oveq123d
    @50
    @14
    @15
    iftrue
    eqtr4d
    @50
    wn
    #
    @54
    @15
    @55
    @56
    cA
    cA
    @51
    cC
    @53
    c.xp
    @56
    @53
    cS
    cvsca
    cfv
    c.xp
    @56
    @52
    cS
    cvsca
    @50
    cR
    cS
    iffalse
    fveq2d
    xpsvsca.n
    syl6eqr
    @56
    cA
    eqidd
    @50
    cB
    cC
    iffalse
    oveq123d
    @50
    @14
    @15
    iffalse
    eqtr4d
    pm2.61i
    @49
    cA
    cA
    @42
    @51
    @44
    @53
    @49
    @43
    @52
    cvsca
    @49
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    @48
    @43
    @52
    wceq
    wph
    @57
    @48
    xpssca.1
    adantr
    wph
    @58
    @48
    xpssca.2
    adantr
    wph
    @48
    simpr
    #
    cR
    cS
    @41
    cV
    cW
    xpscfv
    syl3anc
    fveq2d
    @49
    cA
    eqidd
    @49
    @20
    @21
    @48
    @42
    @51
    wceq
    wph
    @20
    @48
    xpsvsca.4
    adantr
    wph
    @21
    @48
    xpsvsca.5
    adantr
    @59
    cB
    cC
    @41
    cX
    cY
    xpscfv
    syl3anc
    oveq123d
    @49
    @14
    cX
    wcel
    #
    @15
    cY
    wcel
    #
    @48
    @46
    @55
    wceq
    wph
    @60
    @48
    xpsvsca.6
    adantr
    wph
    @61
    @48
    xpsvsca.7
    adantr
    @59
    @14
    @15
    @41
    cX
    cY
    xpscfv
    syl3anc
    3eqtr4a
    mpteq2dva
    wph
    vk
    @9
    cbs
    cfv
    #
    @8
    cG
    @10
    cA
    @0
    c2o
    cK
    cvv
    con0
    @9
    @30
    @62
    eqid
    @36
    xpsvsca.k
    @34
    wph
    @35
    a1i
    c2o
    con0
    wcel
    wph
    2on
    a1i
    wph
    @57
    @58
    @8
    c2o
    wfn
    xpssca.1
    xpssca.2
    cR
    cS
    cV
    cW
    xpscfn
    syl2anc
    xpsvsca.3
    wph
    @0
    @17
    @62
    @29
    @31
    eleqtrd
    prdsvscaval
    wph
    @39
    c2o
    wfn
    #
    @39
    @47
    wceq
    wph
    @60
    @61
    @63
    xpsvsca.6
    xpsvsca.7
    @14
    @15
    cX
    cY
    xpscfn
    syl2anc
    vk
    c2o
    @39
    dffn5
    sylib
    3eqtr4d
    fveq2d
    wph
    @16
    @1
    cfv
    #
    @39
    wceq
    #
    @40
    @16
    wceq
    #
    wph
    @64
    @14
    @15
    @1
    co
    #
    @39
    @14
    @15
    @1
    df-ov
    wph
    @60
    @61
    @67
    @39
    wceq
    xpsvsca.6
    xpsvsca.7
    vx
    vy
    cX
    cY
    @1
    @14
    @15
    @22
    xpsfval
    syl2anc
    syl5eqr
    wph
    @27
    @16
    @24
    wcel
    #
    @65
    @66
    wi
    @28
    wph
    @60
    @61
    @68
    xpsvsca.6
    xpsvsca.7
    @14
    @15
    cX
    cY
    opelxpi
    syl2anc
    @24
    @17
    @16
    @39
    @1
    f1ocnvfv
    sylancr
    mpd
    eqtrd
    3eqtr3d
end
