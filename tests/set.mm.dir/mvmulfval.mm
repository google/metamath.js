include "cop.mm"
include "cmvmul.mm"
include "co.mm"
include "cxp.mm"
include "cmap.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cvv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cbs.mm"
include "cmulr.mm"
include "csb.mm"
include "wceq.mm"
include "df-mvmul.mm"
include "a1i.mm"
include "wa.mm"
include "fvex.mm"
include "xpeq12.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "mpteq1d.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "csbie2.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "cfn.mm"
include "wcel.mm"
include "op1stg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "op2ndg.mm"
include "xpeq12d.mm"
include "oveq12d.mm"
include "oveqd.mm"
include "syl5eq.mm"
include "elex.mm"
include "syl.mm"
include "opex.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "ovmpt2d.mm"

theorem mvmulfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vr: setvar r
  assume mvmulfval.x: |- .X. = ( R maVecMul <. M , N >. )
  assume mvmulfval.b: |- B = ( Base ` R )
  assume mvmulfval.t: |- .x. = ( .r ` R )
  assume mvmulfval.r: |- ( ph -> R e. V )
  assume mvmulfval.m: |- ( ph -> M e. Fin )
  assume mvmulfval.n: |- ( ph -> N e. Fin )

  disjoint i j
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint x y
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint M i
  disjoint M j
  disjoint M x
  disjoint M y
  disjoint N i
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint R i
  disjoint R j
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint B y
  disjoint .x. x
  disjoint .x. y
  disjoint .x. i
  disjoint i m
  disjoint i n
  disjoint i o
  disjoint i r
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j r
  disjoint m n
  disjoint m o
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n o
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint o r
  disjoint o x
  disjoint o y
  disjoint r x
  disjoint r y
  disjoint o ph
  disjoint ph r
  disjoint M o
  disjoint M r
  disjoint N o
  disjoint N r
  disjoint R o
  disjoint R r
  disjoint B o
  disjoint B r
  disjoint .x. o
  disjoint .x. r
  assert |- ( ph -> .X. = ( x e. ( B ^m ( M X. N ) ) , y e. ( B ^m N ) |-> ( i e. M |-> ( R gsum ( j e. N |-> ( ( i x j ) .x. ( y ` j ) ) ) ) ) ) )

  proof
    wph
    c.xp
    cR
    cM
    cN
    cop
    #
    cmvmul
    co
    vx
    vy
    cB
    cM
    cN
    cxp
    #
    cmap
    co
    #
    cB
    cN
    cmap
    co
    #
    vi
    cM
    cR
    vj
    cN
    vi
    cv
    vj
    cv
    #
    vx
    cv
    co
    #
    @4
    vy
    cv
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt2
    #
    mvmulfval.x
    wph
    vr
    vo
    cR
    @0
    cvv
    cvv
    vm
    vo
    cv
    #
    c1st
    cfv
    #
    vn
    @12
    c2nd
    cfv
    #
    vx
    vy
    vr
    cv
    #
    cbs
    cfv
    #
    vm
    cv
    #
    vn
    cv
    #
    cxp
    #
    cmap
    co
    #
    @16
    @18
    cmap
    co
    #
    vi
    @17
    @15
    vj
    @18
    @5
    @6
    @15
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt2
    #
    csb
    csb
    #
    @11
    cmvmul
    cvv
    cmvmul
    vr
    vo
    cvv
    cvv
    @28
    cmpt2
    wceq
    wph
    vx
    vy
    vi
    vj
    vm
    vn
    vo
    vr
    df-mvmul
    a1i
    wph
    @15
    cR
    wceq
    #
    @12
    @0
    wceq
    #
    wa
    #
    wa
    #
    @28
    vx
    vy
    @16
    @13
    @14
    cxp
    #
    cmap
    co
    #
    @16
    @14
    cmap
    co
    #
    vi
    @13
    @15
    vj
    @14
    @23
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt2
    #
    @11
    vm
    vn
    @13
    @14
    @27
    @39
    @12
    c1st
    fvex
    @12
    c2nd
    fvex
    @17
    @13
    wceq
    #
    @18
    @14
    wceq
    #
    wa
    #
    vx
    vy
    @20
    @21
    @26
    @34
    @35
    @38
    @42
    @19
    @33
    @16
    cmap
    @17
    @13
    @18
    @14
    xpeq12
    oveq2d
    @41
    @21
    @35
    wceq
    @40
    @18
    @14
    @16
    cmap
    oveq2
    adantl
    @42
    vi
    @17
    @25
    @13
    @37
    @40
    @41
    simpl
    @42
    @24
    @36
    @15
    cgsu
    @42
    vj
    @18
    @14
    @23
    @40
    @41
    simpr
    mpteq1d
    oveq2d
    mpteq12dv
    mpt2eq123dv
    csbie2
    @32
    vx
    vy
    @34
    @35
    @38
    @2
    @3
    @10
    @32
    @16
    cB
    @33
    @1
    cmap
    @32
    @16
    cR
    cbs
    cfv
    cB
    @32
    @15
    cR
    cbs
    wph
    @29
    @30
    simprl
    #
    fveq2d
    mvmulfval.b
    syl6eqr
    #
    @32
    @13
    cM
    @14
    cN
    @32
    @13
    @0
    c1st
    cfv
    #
    cM
    @30
    @13
    @45
    wceq
    wph
    @29
    @12
    @0
    c1st
    fveq2
    ad2antll
    wph
    @45
    cM
    wceq
    #
    @31
    wph
    cM
    cfn
    wcel
    #
    cN
    cfn
    wcel
    #
    @46
    mvmulfval.m
    mvmulfval.n
    cM
    cN
    cfn
    cfn
    op1stg
    syl2anc
    adantr
    eqtrd
    #
    @32
    @14
    @0
    c2nd
    cfv
    #
    cN
    @30
    @14
    @50
    wceq
    wph
    @29
    @12
    @0
    c2nd
    fveq2
    ad2antll
    wph
    @50
    cN
    wceq
    #
    @31
    wph
    @47
    @48
    @51
    mvmulfval.m
    mvmulfval.n
    cM
    cN
    cfn
    cfn
    op2ndg
    syl2anc
    adantr
    eqtrd
    #
    xpeq12d
    oveq12d
    @32
    @16
    cB
    @14
    cN
    cmap
    @44
    @52
    oveq12d
    @32
    vi
    @13
    @37
    cM
    @9
    @49
    @32
    @15
    cR
    @36
    @8
    cgsu
    @43
    @32
    vj
    @14
    @23
    cN
    @7
    @52
    @32
    @22
    c.x
    @5
    @6
    @32
    @22
    cR
    cmulr
    cfv
    #
    c.x
    @31
    @22
    @53
    wceq
    #
    wph
    @29
    @54
    @30
    @15
    cR
    cmulr
    fveq2
    adantr
    adantl
    mvmulfval.t
    syl6eqr
    oveqd
    mpteq12dv
    oveq12d
    mpteq12dv
    mpt2eq123dv
    syl5eq
    wph
    cR
    cV
    wcel
    cR
    cvv
    wcel
    mvmulfval.r
    cR
    cV
    elex
    syl
    @0
    cvv
    wcel
    wph
    cM
    cN
    opex
    a1i
    @11
    cvv
    wcel
    wph
    vx
    vy
    @2
    @3
    @10
    cB
    @1
    cmap
    ovex
    cB
    cN
    cmap
    ovex
    mpt2ex
    a1i
    ovmpt2d
    syl5eq
end
