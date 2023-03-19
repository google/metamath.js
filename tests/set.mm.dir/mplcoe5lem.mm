include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "ccntz.mm"
include "wss.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wrex.mm"
include "wi.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "mp1i.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "wa.mm"
include "cbs.mm"
include "cmulr.mm"
include "mgpplusg.mm"
include "eqcomi.mm"
include "csrg.mm"
include "crg.mm"
include "mplring.mm"
include "syl2anc.mm"
include "ringsrg.mm"
include "syl.mm"
include "adantr.mm"
include "cmnd.mm"
include "cn0.mm"
include "ringmgp.mm"
include "sseld.mm"
include "imdistani.mm"
include "wf.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "psrbag.mm"
include "mpbid.mm"
include "simpld.mm"
include "ffvelrnda.mm"
include "sselda.mm"
include "mvrcl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "syldan.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "anim12dan.mm"
include "syl11.mm"
include "expd.mm"
include "mpcom.mm"
include "impl.mm"
include "srgpcomp.mm"
include "oveq12.mm"
include "ancoms.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "com23.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "imp32.mm"
include "ralrimivva.mm"
include "syl6eleq.mm"
include "fmptd.mm"
include "frn.mm"
include "sscntz.mm"
include "mpbird.mm"

theorem mplcoe5lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let vf: setvar f
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vl: setvar l
  let vi: setvar i
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cN: class N
  let cX: class X
  let c.x: class .x.
  assume mplcoe1.p: |- P = ( I mPoly R )
  assume mplcoe1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplcoe1.z: |- .0. = ( 0g ` R )
  assume mplcoe1.o: |- .1. = ( 1r ` R )
  assume mplcoe1.i: |- ( ph -> I e. W )
  assume mplcoe2.g: |- G = ( mulGrp ` P )
  assume mplcoe2.m: |- .^ = ( .g ` G )
  assume mplcoe2.v: |- V = ( I mVar R )
  assume mplcoe5.r: |- ( ph -> R e. Ring )
  assume mplcoe5.y: |- ( ph -> Y e. D )
  assume mplcoe5.c: |- ( ph -> A. x e. I A. y e. I ( ( V ` y ) ( +g ` G ) ( V ` x ) ) = ( ( V ` x ) ( +g ` G ) ( V ` y ) ) )
  assume mplcoe5.s: |- ( ph -> S C_ I )

  disjoint S k
  disjoint S y
  disjoint S x
  disjoint k y
  disjoint k x
  disjoint x y
  disjoint Y y
  disjoint ph y
  disjoint k x
  disjoint .^ k
  disjoint .^ x
  disjoint k y
  disjoint .1. k
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint G k
  disjoint G x
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint I f
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint R f
  disjoint R y
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint P k
  disjoint P x
  disjoint V k
  disjoint V x
  disjoint .0. f
  disjoint .0. k
  disjoint .0. x
  disjoint .0. y
  disjoint Y f
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint W k
  disjoint W y
  disjoint G y
  disjoint V y
  disjoint .^ y
  disjoint S l
  disjoint k l
  disjoint l y
  disjoint l x
  disjoint G l
  disjoint V l
  disjoint Y l
  disjoint l y
  disjoint .^ l
  disjoint l ph
  disjoint i k
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint .^ i
  disjoint k n
  disjoint k w
  disjoint k z
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint .^ n
  disjoint w x
  disjoint w z
  disjoint .^ w
  disjoint x z
  disjoint .^ z
  disjoint i y
  disjoint .1. i
  disjoint n y
  disjoint .1. n
  disjoint w y
  disjoint .1. w
  disjoint y z
  disjoint .1. z
  disjoint B k
  disjoint G i
  disjoint G w
  disjoint G z
  disjoint f i
  disjoint f n
  disjoint f w
  disjoint f z
  disjoint I i
  disjoint I n
  disjoint I w
  disjoint I z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint D z
  disjoint P i
  disjoint P w
  disjoint P z
  disjoint V i
  disjoint V n
  disjoint V w
  disjoint V z
  disjoint .0. i
  disjoint .0. n
  disjoint .0. w
  disjoint .0. z
  disjoint X f
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y i
  disjoint Y w
  disjoint Y z
  disjoint W i
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint .x. z
  assert |- ( ph -> ran ( k e. S |-> ( ( Y ` k ) .^ ( V ` k ) ) ) C_ ( ( Cntz ` G ) ` ran ( k e. S |-> ( ( Y ` k ) .^ ( V ` k ) ) ) ) )

  proof
    wph
    vk
    cS
    vk
    cv
    #
    cY
    cfv
    #
    @0
    cV
    cfv
    #
    c.ex
    co
    #
    cmpt
    #
    crn
    #
    @5
    cG
    ccntz
    cfv
    #
    cfv
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @9
    @8
    @10
    co
    #
    wceq
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    wph
    @13
    vx
    vy
    @5
    @5
    wph
    @8
    @5
    wcel
    #
    @9
    @5
    wcel
    #
    @13
    wph
    @15
    @8
    @3
    wceq
    #
    vk
    cS
    wrex
    #
    @16
    @13
    wi
    @8
    cvv
    wcel
    @15
    @18
    wb
    wph
    vx
    vex
    vk
    cS
    @3
    @8
    @4
    cvv
    @4
    eqid
    #
    elrnmpt
    mp1i
    wph
    @16
    @18
    @13
    wph
    @16
    @9
    @3
    wceq
    #
    vk
    cS
    wrex
    #
    @18
    @13
    wi
    #
    @9
    cvv
    wcel
    @16
    @21
    wb
    wph
    vy
    vex
    vk
    cS
    @3
    @9
    @4
    cvv
    @19
    elrnmpt
    mp1i
    @21
    @9
    vl
    cv
    #
    cY
    cfv
    #
    @23
    cV
    cfv
    #
    c.ex
    co
    #
    wceq
    #
    vl
    cS
    wrex
    wph
    @22
    @20
    @27
    vk
    vl
    cS
    @0
    @23
    wceq
    #
    @3
    @26
    @9
    @28
    @1
    @24
    @2
    @25
    c.ex
    @0
    @23
    cY
    fveq2
    @0
    @23
    cV
    fveq2
    oveq12d
    eqeq2d
    cbvrexv
    wph
    @27
    @22
    vl
    cS
    wph
    @23
    cS
    wcel
    #
    wa
    #
    @18
    @27
    @13
    @30
    @17
    @27
    @13
    wi
    vk
    cS
    @30
    @0
    cS
    wcel
    #
    wa
    #
    @17
    @27
    @13
    @32
    @13
    @17
    @27
    wa
    #
    @3
    @26
    @10
    co
    #
    @26
    @3
    @10
    co
    #
    wceq
    @32
    @26
    @2
    cP
    cP
    cbs
    cfv
    #
    @10
    c.ex
    cG
    @1
    @36
    eqid
    #
    cP
    cmulr
    cfv
    #
    @10
    cP
    @38
    cG
    mplcoe2.g
    @38
    eqid
    mgpplusg
    eqcomi
    #
    mplcoe2.g
    mplcoe2.m
    @30
    cP
    csrg
    wcel
    #
    @31
    wph
    @40
    @29
    wph
    cP
    crg
    wcel
    #
    @40
    wph
    cI
    cW
    wcel
    #
    cR
    crg
    wcel
    #
    @41
    mplcoe1.i
    mplcoe5.r
    cP
    cR
    cI
    cW
    mplcoe1.p
    mplring
    syl2anc
    #
    cP
    ringsrg
    syl
    adantr
    adantr
    #
    @30
    @26
    @36
    wcel
    #
    @31
    @30
    cG
    cmnd
    wcel
    #
    @24
    cn0
    wcel
    #
    @25
    @36
    wcel
    #
    @46
    wph
    @47
    @29
    wph
    @41
    @47
    @44
    cP
    cG
    mplcoe2.g
    ringmgp
    syl
    #
    adantr
    @30
    wph
    @23
    cI
    wcel
    #
    wa
    @48
    wph
    @29
    @51
    wph
    cS
    cI
    @23
    mplcoe5.s
    sseld
    imdistani
    wph
    cI
    cn0
    @23
    cY
    wph
    cI
    cn0
    cY
    wf
    #
    cY
    ccnv
    cn
    cima
    cfn
    wcel
    #
    wph
    cY
    cD
    wcel
    #
    @52
    @53
    wa
    #
    mplcoe5.y
    wph
    @42
    @54
    @55
    wb
    mplcoe1.i
    cD
    vf
    cY
    cI
    cW
    mplcoe1.d
    psrbag
    syl
    mpbid
    simpld
    #
    ffvelrnda
    syl
    #
    @30
    @36
    cP
    cR
    cI
    cV
    cW
    @23
    mplcoe1.p
    mplcoe2.v
    @37
    wph
    @42
    @29
    mplcoe1.i
    adantr
    wph
    @43
    @29
    mplcoe5.r
    adantr
    wph
    cS
    cI
    @23
    mplcoe5.s
    sselda
    #
    mvrcl
    #
    @36
    c.ex
    cG
    @24
    @25
    @36
    cP
    cG
    mplcoe2.g
    @37
    mgpbas
    #
    mplcoe2.m
    mulgnn0cl
    syl3anc
    adantr
    wph
    @31
    @2
    @36
    wcel
    @29
    wph
    @31
    wa
    #
    @36
    cP
    cR
    cI
    cV
    cW
    @0
    mplcoe1.p
    mplcoe2.v
    @37
    wph
    @42
    @31
    mplcoe1.i
    adantr
    wph
    @43
    @31
    mplcoe5.r
    adantr
    wph
    cS
    cI
    @0
    mplcoe5.s
    sselda
    #
    mvrcl
    #
    adantlr
    #
    wph
    @31
    @1
    cn0
    wcel
    #
    @29
    wph
    @31
    @0
    cI
    wcel
    #
    @65
    @62
    wph
    cI
    cn0
    @0
    cY
    @56
    ffvelrnda
    #
    syldan
    adantlr
    @32
    @2
    @25
    cP
    @36
    @10
    c.ex
    cG
    @24
    @37
    @39
    mplcoe2.g
    mplcoe2.m
    @45
    @64
    @30
    @49
    @31
    @59
    adantr
    @30
    @48
    @31
    @57
    adantr
    wph
    @29
    @31
    @2
    @25
    @10
    co
    #
    @25
    @2
    @10
    co
    #
    wceq
    #
    @9
    cV
    cfv
    #
    @8
    cV
    cfv
    #
    @10
    co
    #
    @72
    @71
    @10
    co
    #
    wceq
    #
    vy
    cI
    wral
    vx
    cI
    wral
    #
    wph
    @29
    @31
    wa
    #
    @70
    wi
    mplcoe5.c
    @76
    wph
    @77
    @70
    @51
    @66
    wa
    @76
    @70
    wph
    @77
    wa
    @75
    @70
    @71
    @25
    @10
    co
    #
    @25
    @71
    @10
    co
    #
    wceq
    vx
    vy
    @23
    @0
    cI
    cI
    @8
    @23
    wceq
    #
    @73
    @78
    @74
    @79
    @80
    @72
    @25
    @71
    @10
    @8
    @23
    cV
    fveq2
    #
    oveq2d
    @80
    @72
    @25
    @71
    @10
    @81
    oveq1d
    eqeq12d
    @9
    @0
    wceq
    #
    @78
    @68
    @79
    @69
    @82
    @71
    @2
    @25
    @10
    @9
    @0
    cV
    fveq2
    #
    oveq1d
    @82
    @71
    @2
    @25
    @10
    @83
    oveq2d
    eqeq12d
    rspc2v
    wph
    @29
    @51
    @31
    @66
    @58
    @62
    anim12dan
    syl11
    expd
    mpcom
    impl
    srgpcomp
    srgpcomp
    @33
    @11
    @34
    @12
    @35
    @8
    @3
    @9
    @26
    @10
    oveq12
    @27
    @17
    @12
    @35
    wceq
    @9
    @26
    @8
    @3
    @10
    oveq12
    ancoms
    eqeq12d
    syl5ibrcom
    expd
    rexlimdva
    com23
    rexlimdva
    syl5bi
    sylbid
    com23
    sylbid
    imp32
    ralrimivva
    wph
    @5
    cG
    cbs
    cfv
    #
    wss
    #
    @85
    @7
    @14
    wb
    wph
    cS
    @84
    @4
    wf
    @85
    wph
    vk
    cS
    @3
    @84
    @4
    @61
    @47
    @65
    @2
    @84
    wcel
    @3
    @84
    wcel
    wph
    @47
    @31
    @50
    adantr
    @61
    wph
    @66
    wa
    @65
    wph
    @31
    @66
    wph
    cS
    cI
    @0
    mplcoe5.s
    sseld
    imdistani
    @67
    syl
    @61
    @2
    @36
    @84
    @63
    @60
    syl6eleq
    @84
    c.ex
    cG
    @1
    @2
    @84
    eqid
    #
    mplcoe2.m
    mulgnn0cl
    syl3anc
    @19
    fmptd
    cS
    @84
    @4
    frn
    syl
    #
    @87
    vx
    vy
    @84
    @10
    @5
    @5
    cG
    @6
    @86
    @10
    eqid
    @6
    eqid
    sscntz
    syl2anc
    mpbird
end
