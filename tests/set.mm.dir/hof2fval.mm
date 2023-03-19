include "cop.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cvv.mm"
include "chomf.mm"
include "wceq.mm"
include "hofval.mm"
include "fvex.mm"
include "cbs.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "op2ndd.mm"
include "syl.mm"
include "wa.mm"
include "simprr.mm"
include "fveq2d.mm"
include "wcel.mm"
include "op1stg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simprl.mm"
include "oveq12d.mm"
include "op2ndg.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "opeq12d.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "opelxpi.mm"
include "ovex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem hof2fval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cH: class H
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cK: class K
  assume hofval.m: |- M = ( HomF ` C )
  assume hofval.c: |- ( ph -> C e. Cat )
  assume hof1.b: |- B = ( Base ` C )
  assume hof1.h: |- H = ( Hom ` C )
  assume hof1.x: |- ( ph -> X e. B )
  assume hof1.y: |- ( ph -> Y e. B )
  assume hof2.z: |- ( ph -> Z e. B )
  assume hof2.w: |- ( ph -> W e. B )
  assume hof2.o: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f h
  disjoint B f
  disjoint g h
  disjoint B g
  disjoint B h
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint W f
  disjoint W g
  disjoint W h
  disjoint .x. f
  disjoint .x. g
  disjoint .x. h
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint ph y
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint K h
  disjoint W x
  disjoint W y
  disjoint .x. b
  disjoint .x. c
  disjoint .x. x
  disjoint .x. y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) = ( f e. ( Z H X ) , g e. ( Y H W ) |-> ( h e. ( X H Y ) |-> ( ( g ( <. X , Y >. .x. W ) h ) ( <. Z , X >. .x. W ) f ) ) ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cop
    #
    cZ
    cW
    cop
    #
    cB
    cB
    cxp
    #
    @2
    vf
    vg
    vy
    cv
    #
    c1st
    cfv
    #
    vx
    cv
    #
    c1st
    cfv
    #
    cH
    co
    #
    @5
    c2nd
    cfv
    #
    @3
    c2nd
    cfv
    #
    cH
    co
    #
    vh
    @5
    cH
    cfv
    #
    vg
    cv
    #
    vh
    cv
    #
    @5
    @9
    c.x
    co
    #
    co
    #
    vf
    cv
    #
    @4
    @6
    cop
    #
    @9
    c.x
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    vf
    vg
    cZ
    cX
    cH
    co
    #
    cY
    cW
    cH
    co
    #
    vh
    cX
    cY
    cH
    co
    #
    @12
    @13
    @0
    cW
    c.x
    co
    #
    co
    #
    @16
    cZ
    cX
    cop
    #
    cW
    c.x
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cM
    c2nd
    cfv
    #
    cvv
    wph
    cM
    cC
    chomf
    cfv
    #
    vx
    vy
    @2
    @2
    @21
    cmpt2
    #
    cop
    wceq
    @32
    @34
    wceq
    wph
    vx
    vy
    cB
    cC
    c.x
    vf
    vg
    vh
    cH
    cM
    hofval.m
    hofval.c
    hof1.b
    hof1.h
    hof2.o
    hofval
    @33
    @34
    cM
    cC
    chomf
    fvex
    vx
    vy
    @2
    @2
    @21
    cB
    cB
    cB
    cC
    cbs
    cfv
    cvv
    hof1.b
    cC
    cbs
    fvex
    eqeltri
    #
    @35
    xpex
    #
    @36
    mpt2ex
    op2ndd
    syl
    wph
    @5
    @0
    wceq
    #
    @3
    @1
    wceq
    #
    wa
    #
    wa
    #
    vf
    vg
    @7
    @10
    @20
    @22
    @23
    @30
    @40
    @4
    cZ
    @6
    cX
    cH
    @40
    @4
    @1
    c1st
    cfv
    #
    cZ
    @40
    @3
    @1
    c1st
    wph
    @37
    @38
    simprr
    #
    fveq2d
    wph
    @41
    cZ
    wceq
    #
    @39
    wph
    cZ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @43
    hof2.z
    hof2.w
    cZ
    cW
    cB
    cB
    op1stg
    syl2anc
    adantr
    eqtrd
    #
    @40
    @6
    @0
    c1st
    cfv
    #
    cX
    @40
    @5
    @0
    c1st
    wph
    @37
    @38
    simprl
    #
    fveq2d
    wph
    @47
    cX
    wceq
    #
    @39
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @49
    hof1.x
    hof1.y
    cX
    cY
    cB
    cB
    op1stg
    syl2anc
    adantr
    eqtrd
    #
    oveq12d
    @40
    @8
    cY
    @9
    cW
    cH
    @40
    @8
    @0
    c2nd
    cfv
    #
    cY
    @40
    @5
    @0
    c2nd
    @48
    fveq2d
    wph
    @53
    cY
    wceq
    #
    @39
    wph
    @50
    @51
    @54
    hof1.x
    hof1.y
    cX
    cY
    cB
    cB
    op2ndg
    syl2anc
    adantr
    eqtrd
    @40
    @9
    @1
    c2nd
    cfv
    #
    cW
    @40
    @3
    @1
    c2nd
    @42
    fveq2d
    wph
    @55
    cW
    wceq
    #
    @39
    wph
    @44
    @45
    @56
    hof2.z
    hof2.w
    cZ
    cW
    cB
    cB
    op2ndg
    syl2anc
    adantr
    eqtrd
    #
    oveq12d
    @40
    vh
    @11
    @19
    @24
    @29
    @40
    @11
    @0
    cH
    cfv
    @24
    @40
    @5
    @0
    cH
    @48
    fveq2d
    cX
    cY
    cH
    df-ov
    syl6eqr
    @40
    @15
    @26
    @16
    @16
    @18
    @28
    @40
    @17
    @27
    @9
    cW
    c.x
    @40
    @4
    cZ
    @6
    cX
    @46
    @52
    opeq12d
    @57
    oveq12d
    @40
    @14
    @25
    @12
    @13
    @40
    @5
    @0
    @9
    cW
    c.x
    @48
    @57
    oveq12d
    oveqd
    @40
    @16
    eqidd
    oveq123d
    mpteq12dv
    mpt2eq123dv
    wph
    @50
    @51
    @0
    @2
    wcel
    hof1.x
    hof1.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    wph
    @44
    @45
    @1
    @2
    wcel
    hof2.z
    hof2.w
    cZ
    cW
    cB
    cB
    opelxpi
    syl2anc
    @31
    cvv
    wcel
    wph
    vf
    vg
    @22
    @23
    @30
    cZ
    cX
    cH
    ovex
    cY
    cW
    cH
    ovex
    mpt2ex
    a1i
    ovmpt2d
end
