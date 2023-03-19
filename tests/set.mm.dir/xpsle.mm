include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cmpt2.mm"
include "cfv.mm"
include "wbr.mm"
include "csca.mm"
include "cprds.mm"
include "cple.mm"
include "cop.mm"
include "wa.mm"
include "crn.mm"
include "wcel.mm"
include "wb.mm"
include "df-ov.mm"
include "wceq.mm"
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
include "f1olecpbl.mm"
include "imasleval.mm"
include "mpd3an23.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "sylancr.mm"
include "mpd.mm"
include "breq12d.mm"
include "c2o.mm"
include "wral.mm"
include "cbs.mm"
include "con0.mm"
include "fvexd.mm"
include "2on.mm"
include "a1i.mm"
include "wfn.mm"
include "xpscfn.mm"
include "eleqtrd.mm"
include "prdsleval.mm"
include "c0.mm"
include "c1o.mm"
include "cpr.mm"
include "df2o3.mm"
include "raleqi.mm"
include "0ex.mm"
include "1on.mm"
include "elexi.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq123d.mm"
include "ralpr.mm"
include "bitri.mm"
include "xpsc0.mm"
include "syl6eqr.mm"
include "xpsc1.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "3bitr3d.mm"

theorem xpsle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  assume xpsle.t: |- T = ( R Xs. S )
  assume xpsle.x: |- X = ( Base ` R )
  assume xpsle.y: |- Y = ( Base ` S )
  assume xpsle.1: |- ( ph -> R e. V )
  assume xpsle.2: |- ( ph -> S e. W )
  assume xpsle.p: |- .<_ = ( le ` T )
  assume xpsle.m: |- M = ( le ` R )
  assume xpsle.n: |- N = ( le ` S )
  assume xpsle.3: |- ( ph -> A e. X )
  assume xpsle.4: |- ( ph -> B e. Y )
  assume xpsle.5: |- ( ph -> C e. X )
  assume xpsle.6: |- ( ph -> D e. Y )


  assert |- ( ph -> ( <. A , B >. .<_ <. C , D >. <-> ( A M C /\ B N D ) ) )

  proof
    wph
    cA
    csn
    cB
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
    cC
    csn
    cD
    csn
    ccda
    co
    ccnv
    #
    @2
    cfv
    #
    c.le
    wbr
    #
    @0
    @4
    cR
    csca
    cfv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cprds
    co
    #
    cple
    cfv
    #
    wbr
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    c.le
    wbr
    cA
    cC
    cM
    wbr
    #
    cB
    cD
    cN
    wbr
    #
    wa
    #
    wph
    @0
    @1
    crn
    #
    wcel
    @4
    @17
    wcel
    @6
    @11
    wb
    wph
    @12
    @1
    cfv
    #
    @0
    @17
    wph
    @18
    cA
    cB
    @1
    co
    #
    @0
    cA
    cB
    @1
    df-ov
    wph
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    @19
    @0
    wceq
    xpsle.3
    xpsle.4
    vx
    vy
    cX
    cY
    @1
    cA
    cB
    @1
    eqid
    #
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @12
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
    xpsle.3
    xpsle.4
    cA
    cB
    cX
    cY
    opelxpi
    syl2anc
    #
    @24
    @17
    @12
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
    #
    ffvelrni
    syl
    eqeltrrd
    #
    wph
    @13
    @1
    cfv
    #
    @4
    @17
    wph
    @31
    cC
    cD
    @1
    co
    #
    @4
    cC
    cD
    @1
    df-ov
    wph
    cC
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    @32
    @4
    wceq
    xpsle.5
    xpsle.6
    vx
    vy
    cX
    cY
    @1
    cC
    cD
    @22
    xpsfval
    syl2anc
    syl5eqr
    #
    wph
    @13
    @24
    wcel
    #
    @31
    @17
    wcel
    wph
    @33
    @34
    @36
    xpsle.5
    xpsle.6
    cC
    cD
    cX
    cY
    opelxpi
    syl2anc
    #
    @24
    @17
    @13
    @1
    @29
    ffvelrni
    syl
    eqeltrrd
    #
    wph
    @24
    @9
    cT
    @2
    c.le
    @10
    @17
    @0
    @4
    cvv
    va
    vb
    vc
    vd
    wph
    vx
    vy
    cR
    cS
    cT
    @9
    @1
    @7
    cV
    cW
    cX
    cY
    xpsle.t
    xpsle.x
    xpsle.y
    xpsle.1
    xpsle.2
    @22
    @7
    eqid
    #
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
    @7
    cV
    cW
    cX
    cY
    xpsle.t
    xpsle.x
    xpsle.y
    xpsle.1
    xpsle.2
    @22
    @39
    @40
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
    @42
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
    @7
    @8
    cprds
    ovexd
    xpsle.p
    @10
    eqid
    #
    wph
    va
    cv
    vb
    cv
    vc
    cv
    vd
    cv
    @2
    @10
    @17
    @24
    @43
    f1olecpbl
    imasleval
    mpd3an23
    wph
    @3
    @12
    @5
    @13
    c.le
    wph
    @18
    @0
    wceq
    #
    @3
    @12
    wceq
    #
    @23
    wph
    @27
    @25
    @45
    @46
    wi
    @28
    @26
    @24
    @17
    @12
    @0
    @1
    f1ocnvfv
    sylancr
    mpd
    wph
    @31
    @4
    wceq
    #
    @5
    @13
    wceq
    #
    @35
    wph
    @27
    @36
    @47
    @48
    wi
    @28
    @37
    @24
    @17
    @13
    @4
    @1
    f1ocnvfv
    sylancr
    mpd
    breq12d
    wph
    @11
    vk
    cv
    #
    @0
    cfv
    #
    @49
    @4
    cfv
    #
    @49
    @8
    cfv
    #
    cple
    cfv
    #
    wbr
    #
    vk
    c2o
    wral
    #
    @16
    wph
    vk
    @9
    cbs
    cfv
    #
    @8
    @7
    @0
    @4
    c2o
    @10
    cvv
    con0
    @9
    @40
    @56
    eqid
    wph
    cR
    csca
    fvexd
    c2o
    con0
    wcel
    wph
    2on
    a1i
    wph
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    @8
    c2o
    wfn
    xpsle.1
    xpsle.2
    cR
    cS
    cV
    cW
    xpscfn
    syl2anc
    wph
    @0
    @17
    @56
    @30
    @41
    eleqtrd
    wph
    @4
    @17
    @56
    @38
    @41
    eleqtrd
    @44
    prdsleval
    @55
    c0
    @0
    cfv
    #
    c0
    @4
    cfv
    #
    c0
    @8
    cfv
    #
    cple
    cfv
    #
    wbr
    #
    c1o
    @0
    cfv
    #
    c1o
    @4
    cfv
    #
    c1o
    @8
    cfv
    #
    cple
    cfv
    #
    wbr
    #
    wa
    #
    wph
    @16
    @55
    @54
    vk
    c0
    c1o
    cpr
    #
    wral
    @69
    @54
    vk
    c2o
    @70
    df2o3
    raleqi
    @54
    @63
    @68
    vk
    c0
    c1o
    0ex
    c1o
    con0
    1on
    elexi
    @49
    c0
    wceq
    #
    @50
    @59
    @51
    @60
    @53
    @62
    @49
    c0
    @0
    fveq2
    @71
    @52
    @61
    cple
    @49
    c0
    @8
    fveq2
    fveq2d
    @49
    c0
    @4
    fveq2
    breq123d
    @49
    c1o
    wceq
    #
    @50
    @64
    @51
    @65
    @53
    @67
    @49
    c1o
    @0
    fveq2
    @72
    @52
    @66
    cple
    @49
    c1o
    @8
    fveq2
    fveq2d
    @49
    c1o
    @4
    fveq2
    breq123d
    ralpr
    bitri
    wph
    @63
    @14
    @68
    @15
    wph
    @59
    cA
    @60
    cC
    @62
    cM
    wph
    @20
    @59
    cA
    wceq
    xpsle.3
    cA
    cB
    cX
    xpsc0
    syl
    wph
    @62
    cR
    cple
    cfv
    cM
    wph
    @61
    cR
    cple
    wph
    @57
    @61
    cR
    wceq
    xpsle.1
    cR
    cS
    cV
    xpsc0
    syl
    fveq2d
    xpsle.m
    syl6eqr
    wph
    @33
    @60
    cC
    wceq
    xpsle.5
    cC
    cD
    cX
    xpsc0
    syl
    breq123d
    wph
    @64
    cB
    @65
    cD
    @67
    cN
    wph
    @21
    @64
    cB
    wceq
    xpsle.4
    cA
    cB
    cY
    xpsc1
    syl
    wph
    @67
    cS
    cple
    cfv
    cN
    wph
    @66
    cS
    cple
    wph
    @58
    @66
    cS
    wceq
    xpsle.2
    cR
    cS
    cW
    xpsc1
    syl
    fveq2d
    xpsle.n
    syl6eqr
    wph
    @34
    @65
    cD
    wceq
    xpsle.6
    cC
    cD
    cY
    xpsc1
    syl
    breq123d
    anbi12d
    syl5bb
    bitrd
    3bitr3d
end
