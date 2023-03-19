include "cv.mm"
include "cdg1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cco1.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cmulr.mm"
include "crg.mm"
include "cbs.mm"
include "ad2antrr.mm"
include "ply1ring.mm"
include "syl.mm"
include "cmnd.mm"
include "cn0.mm"
include "eqid.mm"
include "ringmgp.mm"
include "nn0sub2.mm"
include "syl3anc.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "simplr.mm"
include "lidlmcl.mm"
include "syl22anc.mm"
include "caddc.mm"
include "wss.mm"
include "lidlss.mm"
include "sseldd.mm"
include "deg1pwle.mm"
include "syl2anc.mm"
include "simpr.mm"
include "deg1mulle2.mm"
include "nn0cnd.mm"
include "npcand.mm"
include "breqtrd.mm"
include "c0g.mm"
include "coe1pwmulfv.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "ss2abdv.mm"
include "hbtlem1.mm"
include "3sstr4d.mm"

theorem hbtlem4
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  assume hbtlem.p: |- P = ( Poly1 ` R )
  assume hbtlem.u: |- U = ( LIdeal ` P )
  assume hbtlem.s: |- S = ( ldgIdlSeq ` R )
  assume hbtlem4.r: |- ( ph -> R e. Ring )
  assume hbtlem4.i: |- ( ph -> I e. U )
  assume hbtlem4.x: |- ( ph -> X e. NN0 )
  assume hbtlem4.y: |- ( ph -> Y e. NN0 )
  assume hbtlem4.xy: |- ( ph -> X <_ Y )


  assert |- ( ph -> ( ( S ` I ) ` X ) C_ ( ( S ` I ) ` Y ) )

  proof
    wph
    vc
    cv
    #
    cR
    cdg1
    cfv
    #
    cfv
    cX
    cle
    wbr
    #
    va
    cv
    #
    cX
    @0
    cco1
    cfv
    cfv
    #
    wceq
    #
    wa
    #
    vc
    cI
    wrex
    #
    va
    cab
    #
    vb
    cv
    #
    @1
    cfv
    #
    cY
    cle
    wbr
    #
    @3
    cY
    @9
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vb
    cI
    wrex
    #
    va
    cab
    #
    cX
    cI
    cS
    cfv
    #
    cfv
    #
    cY
    @18
    cfv
    #
    wph
    @7
    @16
    va
    wph
    @6
    @16
    vc
    cI
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @2
    @5
    @16
    @22
    @2
    wa
    #
    @16
    @5
    @11
    @4
    @13
    wceq
    #
    wa
    #
    vb
    cI
    wrex
    #
    @23
    cY
    cX
    cmin
    co
    #
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @0
    cP
    cmulr
    cfv
    #
    co
    #
    cI
    wcel
    #
    @33
    @1
    cfv
    #
    cY
    cle
    wbr
    #
    @4
    cY
    @33
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    @26
    @23
    cP
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    @31
    cP
    cbs
    cfv
    #
    wcel
    #
    @21
    @34
    @23
    cR
    crg
    wcel
    #
    @40
    wph
    @44
    @21
    @2
    hbtlem4.r
    ad2antrr
    #
    cP
    cR
    hbtlem.p
    ply1ring
    syl
    #
    wph
    @41
    @21
    @2
    hbtlem4.i
    ad2antrr
    #
    @23
    @29
    cmnd
    wcel
    #
    @27
    cn0
    wcel
    #
    @28
    @42
    wcel
    #
    @43
    @23
    @40
    @48
    @46
    cP
    @29
    @29
    eqid
    #
    ringmgp
    syl
    @23
    cX
    cn0
    wcel
    #
    cY
    cn0
    wcel
    #
    cX
    cY
    cle
    wbr
    #
    @49
    wph
    @52
    @21
    @2
    hbtlem4.x
    ad2antrr
    #
    wph
    @53
    @21
    @2
    hbtlem4.y
    ad2antrr
    #
    wph
    @54
    @21
    @2
    hbtlem4.xy
    ad2antrr
    cX
    cY
    nn0sub2
    syl3anc
    #
    @23
    @44
    @50
    @45
    @42
    cP
    cR
    @28
    @28
    eqid
    #
    hbtlem.p
    @42
    eqid
    #
    vr1cl
    syl
    @42
    @30
    @29
    @27
    @28
    @42
    cP
    @29
    @51
    @59
    mgpbas
    @30
    eqid
    #
    mulgnn0cl
    syl3anc
    #
    wph
    @21
    @2
    simplr
    #
    @42
    cP
    @32
    cU
    cI
    @31
    @0
    hbtlem.u
    @59
    @32
    eqid
    #
    lidlmcl
    syl22anc
    @23
    @35
    @27
    cX
    caddc
    co
    #
    cY
    cle
    @23
    @42
    @1
    cR
    @32
    @31
    @0
    @27
    cX
    cP
    hbtlem.p
    @1
    eqid
    #
    @45
    @59
    @63
    @61
    @23
    cI
    @42
    @0
    @23
    @41
    cI
    @42
    wss
    @47
    @42
    cI
    cU
    cP
    @59
    hbtlem.u
    lidlss
    syl
    @62
    sseldd
    #
    @57
    @55
    @23
    @44
    @49
    @31
    @1
    cfv
    @27
    cle
    wbr
    @45
    @57
    @1
    cP
    cR
    @30
    @27
    @29
    @28
    @65
    hbtlem.p
    @58
    @51
    @60
    deg1pwle
    syl2anc
    @22
    @2
    simpr
    deg1mulle2
    @23
    cY
    cX
    @23
    cY
    @56
    nn0cnd
    @23
    cX
    @55
    nn0cnd
    npcand
    #
    breqtrd
    @23
    @64
    @37
    cfv
    @4
    @38
    @23
    @0
    @42
    @27
    cP
    cR
    @32
    @30
    @29
    @28
    cX
    cR
    c0g
    cfv
    #
    @68
    eqid
    hbtlem.p
    @58
    @51
    @60
    @59
    @63
    @45
    @66
    @57
    @55
    coe1pwmulfv
    @23
    @64
    cY
    @37
    @67
    fveq2d
    eqtr3d
    @25
    @36
    @39
    wa
    vb
    @33
    cI
    @9
    @33
    wceq
    #
    @11
    @36
    @24
    @39
    @69
    @10
    @35
    cY
    cle
    @9
    @33
    @1
    fveq2
    breq1d
    @69
    @13
    @38
    @4
    @69
    cY
    @12
    @37
    @9
    @33
    cco1
    fveq2
    fveq1d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @5
    @15
    @25
    vb
    cI
    @5
    @14
    @24
    @11
    @3
    @4
    @13
    eqeq1
    anbi2d
    rexbidv
    syl5ibrcom
    expimpd
    rexlimdva
    ss2abdv
    wph
    @44
    @41
    @52
    @19
    @8
    wceq
    hbtlem4.r
    hbtlem4.i
    hbtlem4.x
    @1
    cP
    cR
    cS
    cU
    va
    vc
    cI
    crg
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @65
    hbtlem1
    syl3anc
    wph
    @44
    @41
    @53
    @20
    @17
    wceq
    hbtlem4.r
    hbtlem4.i
    hbtlem4.y
    @1
    cP
    cR
    cS
    cU
    va
    vb
    cI
    crg
    cY
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @65
    hbtlem1
    syl3anc
    3sstr4d
end
