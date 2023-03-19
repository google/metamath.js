include "cur.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "eqid.mm"
include "wcel.mm"
include "cfn.mm"
include "cbs.mm"
include "cmat.mm"
include "fveq2i.mm"
include "mat1bas.mm"
include "syl2anc.mm"
include "mavmulval.mm"
include "wa.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "wceq.mm"
include "mat1.mm"
include "oveqdr.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "cvv.mm"
include "eqidd.mm"
include "eqeq12.mm"
include "ifbid.mm"
include "adantl.mm"
include "simpr.mm"
include "adantr.mm"
include "fvexd.mm"
include "ifcld.mm"
include "ovmpt2d.mm"
include "iftrue.mm"
include "wi.mm"
include "cmap.mm"
include "wf.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elmapd.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl6bi.mm"
include "mpd.mm"
include "imp.mm"
include "ringlidm.mm"
include "fveq2.mm"
include "equcoms.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "ringlz.mm"
include "eqcom.mm"
include "sylnbi.mm"
include "eqcomd.mm"
include "pm2.61ian.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "syl.mm"
include "syl6eleq.mm"
include "gsummptif1n0.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn5.mm"
include "bitr4i.mm"
include "sylibr.mm"

theorem 1mavmul
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume 1mavmul.a: |- A = ( N Mat R )
  assume 1mavmul.b: |- B = ( Base ` R )
  assume 1mavmul.t: |- .x. = ( R maVecMul <. N , N >. )
  assume 1mavmul.r: |- ( ph -> R e. Ring )
  assume 1mavmul.n: |- ( ph -> N e. Fin )
  assume 1mavmul.y: |- ( ph -> Y e. ( B ^m N ) )


  assert |- ( ph -> ( ( 1r ` A ) .x. Y ) = Y )

  proof
    wph
    cA
    cur
    cfv
    #
    cY
    c.x
    co
    vi
    cN
    cR
    vj
    cN
    vi
    cv
    #
    vj
    cv
    #
    @0
    co
    #
    @2
    cY
    cfv
    #
    cR
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
    vi
    cN
    @1
    cY
    cfv
    #
    cmpt
    #
    cY
    wph
    cA
    cB
    cR
    @5
    c.x
    vi
    vj
    cN
    crg
    @0
    cY
    1mavmul.a
    1mavmul.t
    1mavmul.b
    @5
    eqid
    #
    1mavmul.r
    1mavmul.n
    wph
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    @0
    cA
    cbs
    cfv
    #
    wcel
    1mavmul.r
    1mavmul.n
    cA
    @14
    cR
    @0
    cN
    1mavmul.a
    @14
    eqid
    cA
    cN
    cR
    cmat
    co
    cur
    1mavmul.a
    fveq2i
    mat1bas
    syl2anc
    1mavmul.y
    mavmulval
    wph
    vi
    cN
    @8
    @9
    wph
    @1
    cN
    wcel
    #
    wa
    #
    @8
    cR
    vj
    cN
    @1
    @2
    vx
    vy
    cN
    cN
    vx
    vy
    weq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt2
    #
    co
    #
    @4
    @5
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vj
    cN
    vj
    vi
    weq
    #
    @9
    @19
    cif
    #
    cmpt
    #
    cgsu
    co
    @9
    @16
    @7
    @24
    cR
    cgsu
    @16
    vj
    cN
    @6
    @23
    @16
    @3
    @22
    @4
    @5
    wph
    @15
    vi
    vj
    @0
    @21
    wph
    @13
    @12
    @0
    @21
    wceq
    1mavmul.n
    1mavmul.r
    cA
    cR
    @18
    vx
    vy
    cN
    @19
    1mavmul.a
    @18
    eqid
    #
    @19
    eqid
    #
    mat1
    syl2anc
    oveqdr
    oveq1d
    mpteq2dv
    oveq2d
    @16
    @24
    @27
    cR
    cgsu
    @16
    vj
    cN
    @23
    @26
    @16
    @2
    cN
    wcel
    #
    wa
    #
    @23
    vi
    vj
    weq
    #
    @18
    @19
    cif
    #
    @4
    @5
    co
    #
    @26
    @31
    @22
    @33
    @4
    @5
    @31
    vx
    vy
    @1
    @2
    cN
    cN
    @20
    @33
    @21
    cvv
    @31
    @21
    eqidd
    vx
    vi
    weq
    vy
    vj
    weq
    wa
    #
    @20
    @33
    wceq
    @31
    @35
    @17
    @32
    @18
    @19
    vx
    cv
    @1
    vy
    cv
    @2
    eqeq12
    ifbid
    adantl
    @16
    @15
    @30
    wph
    @15
    simpr
    #
    adantr
    @16
    @30
    simpr
    @31
    @32
    @18
    @19
    cvv
    @31
    cR
    cur
    fvexd
    @31
    cR
    c0g
    fvexd
    ifcld
    ovmpt2d
    oveq1d
    @32
    @31
    @34
    @26
    wceq
    @32
    @31
    wa
    #
    @34
    @9
    @26
    @37
    @34
    @18
    @4
    @5
    co
    #
    @4
    @9
    @37
    @33
    @18
    @4
    @5
    @32
    @33
    @18
    wceq
    @31
    @32
    @18
    @19
    iftrue
    adantr
    oveq1d
    @31
    @38
    @4
    wceq
    #
    @32
    @31
    @12
    @4
    cB
    wcel
    #
    @39
    @16
    @12
    @30
    wph
    @12
    @15
    1mavmul.r
    adantr
    adantr
    #
    @16
    @30
    @40
    wph
    @30
    @40
    wi
    #
    @15
    wph
    cY
    cB
    cN
    cmap
    co
    wcel
    #
    @42
    1mavmul.y
    wph
    @43
    cN
    cB
    cY
    wf
    #
    @42
    wph
    cB
    cN
    cY
    cvv
    cfn
    cB
    cvv
    wcel
    wph
    cB
    cR
    cbs
    cfv
    #
    cvv
    1mavmul.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    1mavmul.n
    elmapd
    #
    @44
    @30
    @40
    cN
    cB
    @2
    cY
    ffvelrn
    ex
    syl6bi
    mpd
    adantr
    imp
    #
    cB
    cR
    @5
    @18
    @4
    1mavmul.b
    @11
    @28
    ringlidm
    syl2anc
    adantl
    @32
    @4
    @9
    wceq
    #
    @31
    @48
    vj
    vi
    @2
    @1
    cY
    fveq2
    equcoms
    adantr
    3eqtrd
    @32
    @26
    @9
    wceq
    #
    @31
    @49
    vj
    vi
    @25
    @9
    @19
    iftrue
    equcoms
    adantr
    eqtr4d
    @32
    wn
    #
    @31
    wa
    @34
    @19
    @4
    @5
    co
    #
    @19
    @26
    @50
    @34
    @51
    wceq
    @31
    @50
    @33
    @19
    @4
    @5
    @32
    @18
    @19
    iffalse
    oveq1d
    adantr
    @31
    @51
    @19
    wceq
    #
    @50
    @31
    @12
    @40
    @52
    @41
    @47
    cB
    cR
    @5
    @4
    @19
    1mavmul.b
    @11
    @29
    ringlz
    syl2anc
    adantl
    @50
    @19
    @26
    wceq
    @31
    @50
    @26
    @19
    @32
    @25
    @26
    @19
    wceq
    @1
    @2
    eqcom
    @25
    @9
    @19
    iffalse
    sylnbi
    eqcomd
    adantr
    3eqtrd
    pm2.61ian
    eqtrd
    mpteq2dva
    oveq2d
    @16
    @9
    vj
    @27
    cR
    cN
    cfn
    @1
    @19
    @29
    wph
    cR
    cmnd
    wcel
    #
    @15
    wph
    @12
    @53
    1mavmul.r
    cR
    ringmnd
    syl
    adantr
    wph
    @13
    @15
    1mavmul.n
    adantr
    @36
    @27
    eqid
    wph
    @15
    @9
    @45
    wcel
    #
    wph
    @43
    @15
    @54
    wi
    #
    1mavmul.y
    wph
    @43
    @44
    @55
    @46
    @44
    @15
    @54
    @44
    @15
    wa
    @9
    cB
    @45
    cN
    cB
    @1
    cY
    ffvelrn
    1mavmul.b
    syl6eleq
    ex
    syl6bi
    mpd
    imp
    gsummptif1n0
    3eqtrd
    mpteq2dva
    wph
    cY
    cN
    wfn
    #
    @10
    cY
    wceq
    #
    wph
    @43
    @56
    1mavmul.y
    wph
    @43
    @44
    @56
    @46
    cN
    cB
    cY
    ffn
    syl6bi
    mpd
    @57
    cY
    @10
    wceq
    @56
    @10
    cY
    eqcom
    vi
    cN
    cY
    dffn5
    bitr4i
    sylibr
    3eqtrd
end
