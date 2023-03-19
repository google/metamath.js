include "copws.mm"
include "co.mm"
include "cfv.mm"
include "cnx.mm"
include "cple.mm"
include "cop.mm"
include "csts.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wbr.mm"
include "cltb.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wo.mm"
include "copab.mm"
include "cxp.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "elex.mm"
include "syl.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "cmps.mm"
include "cbs.mm"
include "cplt.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wsbc.mm"
include "csb.mm"
include "simpl.mm"
include "sqxpeqd.mm"
include "pweqd.mm"
include "ovexd.mm"
include "id.mm"
include "oveq12.mm"
include "sylan9eqr.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "sseq2d.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "adantr.mm"
include "oveq2d.mm"
include "rabeq.mm"
include "simpr.mm"
include "simpllr.mm"
include "breqd.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "sbcied2.mm"
include "orbi1d.mm"
include "opabbidv.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "csbied.mm"
include "mpteq12dv.mm"
include "df-opsr.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem opsrval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cT: class T
  let vh: setvar h
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vi: setvar i
  let vp: setvar p
  let vs: setvar s
  let vd: setvar d
  assume opsrval.s: |- S = ( I mPwSer R )
  assume opsrval.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrval.b: |- B = ( Base ` S )
  assume opsrval.q: |- .< = ( lt ` R )
  assume opsrval.c: |- C = ( T <bag I )
  assume opsrval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume opsrval.l: |- .<_ = { <. x , y >. | ( { x , y } C_ B /\ ( E. z e. D ( ( x ` z ) .< ( y ` z ) /\ A. w e. D ( w C z -> ( x ` w ) = ( y ` w ) ) ) \/ x = y ) ) }
  assume opsrval.i: |- ( ph -> I e. V )
  assume opsrval.r: |- ( ph -> R e. W )
  assume opsrval.t: |- ( ph -> T C_ ( I X. I ) )

  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint .<_ r
  disjoint i p
  disjoint i s
  disjoint B i
  disjoint p s
  disjoint B p
  disjoint B s
  disjoint d h
  disjoint d i
  disjoint d p
  disjoint d r
  disjoint d s
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint h i
  disjoint h p
  disjoint h r
  disjoint h s
  disjoint i r
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint p r
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint I p
  disjoint r s
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint I s
  disjoint ph r
  disjoint .< d
  disjoint .< i
  disjoint .< p
  disjoint .< s
  disjoint D d
  disjoint D i
  disjoint D p
  disjoint D s
  disjoint S i
  disjoint S p
  disjoint S r
  disjoint S s
  disjoint T r
  disjoint R d
  disjoint R i
  disjoint R p
  disjoint R r
  disjoint R s
  assert |- ( ph -> O = ( S sSet <. ( le ` ndx ) , .<_ >. ) )

  proof
    wph
    cO
    cT
    cI
    cR
    copws
    co
    #
    cfv
    cS
    cnx
    cple
    cfv
    #
    c.le
    cop
    #
    csts
    co
    #
    opsrval.o
    wph
    vr
    cT
    cS
    @1
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cB
    wss
    #
    vz
    cv
    #
    @4
    cfv
    #
    @8
    @5
    cfv
    #
    c.lt
    wbr
    #
    vw
    cv
    #
    @8
    vr
    cv
    #
    cI
    cltb
    co
    #
    wbr
    #
    @12
    @4
    cfv
    @12
    @5
    cfv
    wceq
    #
    wi
    #
    vw
    cD
    wral
    #
    wa
    #
    vz
    cD
    wrex
    #
    @4
    @5
    wceq
    #
    wo
    #
    wa
    #
    vx
    vy
    copab
    #
    cop
    #
    csts
    co
    #
    @3
    cI
    cI
    cxp
    #
    cpw
    #
    @0
    cvv
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    vr
    @28
    @26
    cmpt
    #
    cvv
    wcel
    #
    @0
    @31
    wceq
    wph
    cI
    cV
    wcel
    #
    @29
    opsrval.i
    cI
    cV
    elex
    syl
    wph
    cR
    cW
    wcel
    @30
    opsrval.r
    cR
    cW
    elex
    syl
    wph
    @27
    cvv
    wcel
    #
    @28
    cvv
    wcel
    @32
    wph
    @33
    @33
    @34
    opsrval.i
    opsrval.i
    cI
    cI
    cV
    cV
    xpexg
    syl2anc
    #
    @27
    cvv
    pwexg
    vr
    @28
    @26
    cvv
    mptexg
    3syl
    vi
    vs
    cI
    cR
    cvv
    cvv
    vr
    vi
    cv
    #
    @36
    cxp
    #
    cpw
    #
    vp
    @36
    vs
    cv
    #
    cmps
    co
    #
    vp
    cv
    #
    @1
    @6
    @41
    cbs
    cfv
    #
    wss
    #
    @9
    @10
    @39
    cplt
    cfv
    #
    wbr
    #
    @12
    @8
    @13
    @36
    cltb
    co
    #
    wbr
    #
    @16
    wi
    #
    vw
    vd
    cv
    #
    wral
    #
    wa
    #
    vz
    @49
    wrex
    #
    vd
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vh
    cn0
    @36
    cmap
    co
    #
    crab
    #
    wsbc
    #
    @21
    wo
    #
    wa
    #
    vx
    vy
    copab
    #
    cop
    #
    csts
    co
    #
    csb
    #
    cmpt
    @31
    copws
    cvv
    @36
    cI
    wceq
    #
    @39
    cR
    wceq
    #
    wa
    #
    vr
    @38
    @62
    @28
    @26
    @65
    @37
    @27
    @65
    @36
    cI
    @63
    @64
    simpl
    #
    sqxpeqd
    pweqd
    @65
    vp
    @40
    @61
    @26
    cvv
    @65
    @36
    @39
    cmps
    ovexd
    @65
    @41
    @40
    wceq
    #
    wa
    #
    @41
    cS
    @60
    @25
    csts
    @68
    @41
    cI
    cR
    cmps
    co
    #
    cS
    @67
    @65
    @41
    @40
    @69
    @67
    id
    @36
    cI
    @39
    cR
    cmps
    oveq12
    sylan9eqr
    opsrval.s
    syl6eqr
    #
    @68
    @59
    @24
    @1
    @68
    @58
    @23
    vx
    vy
    @68
    @43
    @7
    @57
    @22
    @68
    @42
    cB
    @6
    @68
    @42
    cS
    cbs
    cfv
    cB
    @68
    @41
    cS
    cbs
    @70
    fveq2d
    opsrval.b
    syl6eqr
    sseq2d
    @68
    @56
    @20
    @21
    @68
    @52
    @20
    vd
    @55
    cD
    cvv
    @55
    cvv
    wcel
    @68
    @53
    vh
    @54
    cn0
    @36
    cmap
    ovex
    rabex
    a1i
    @68
    @55
    @53
    vh
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cD
    @68
    @54
    @71
    wceq
    @55
    @72
    wceq
    @68
    @36
    cI
    cn0
    cmap
    @65
    @63
    @67
    @66
    adantr
    #
    oveq2d
    @53
    vh
    @54
    @71
    rabeq
    syl
    opsrval.d
    syl6eqr
    @68
    @49
    cD
    wceq
    #
    wa
    #
    @51
    @19
    vz
    @49
    cD
    @68
    @74
    simpr
    #
    @75
    @45
    @11
    @50
    @18
    @75
    @44
    c.lt
    @9
    @10
    @75
    @44
    cR
    cplt
    cfv
    c.lt
    @75
    @39
    cR
    cplt
    @63
    @64
    @67
    @74
    simpllr
    fveq2d
    opsrval.q
    syl6eqr
    breqd
    @75
    @48
    @17
    vw
    @49
    cD
    @76
    @75
    @47
    @15
    @16
    @75
    @46
    @14
    @12
    @8
    @75
    @36
    cI
    @13
    cltb
    @68
    @63
    @74
    @73
    adantr
    oveq2d
    breqd
    imbi1d
    raleqbidv
    anbi12d
    rexeqbidv
    sbcied2
    orbi1d
    anbi12d
    opabbidv
    opeq2d
    oveq12d
    csbied
    mpteq12dv
    vx
    vy
    vz
    vw
    vh
    vi
    vs
    vr
    vp
    vd
    df-opsr
    ovmpt2ga
    syl3anc
    wph
    @13
    cT
    wceq
    #
    wa
    #
    @25
    @2
    cS
    csts
    @78
    @24
    c.le
    @1
    @78
    @24
    @7
    @11
    @12
    @8
    cC
    wbr
    #
    @16
    wi
    #
    vw
    cD
    wral
    #
    wa
    #
    vz
    cD
    wrex
    #
    @21
    wo
    #
    wa
    #
    vx
    vy
    copab
    c.le
    @78
    @23
    @85
    vx
    vy
    @78
    @22
    @84
    @7
    @78
    @20
    @83
    @21
    @78
    @19
    @82
    vz
    cD
    @78
    @18
    @81
    @11
    @78
    @17
    @80
    vw
    cD
    @78
    @15
    @79
    @16
    @78
    @14
    cC
    @12
    @8
    @78
    @14
    cT
    cI
    cltb
    co
    cC
    @78
    @13
    cT
    cI
    cltb
    wph
    @77
    simpr
    oveq1d
    opsrval.c
    syl6eqr
    breqd
    imbi1d
    ralbidv
    anbi2d
    rexbidv
    orbi1d
    anbi2d
    opabbidv
    opsrval.l
    syl6eqr
    opeq2d
    oveq2d
    wph
    cT
    @28
    wcel
    #
    cT
    @27
    wss
    #
    opsrval.t
    wph
    @34
    @86
    @87
    wb
    @35
    cT
    @27
    cvv
    elpw2g
    syl
    mpbird
    wph
    cS
    @2
    csts
    ovexd
    fvmptd
    syl5eq
end
