include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "cmap.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "c0g.mm"
include "eqid.mm"
include "crg.mm"
include "ccmn.mm"
include "adantr.mm"
include "ringcmn.mm"
include "syl.mm"
include "cvv.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "elbasov.mm"
include "simpld.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "ad2antrr.mm"
include "psrelbas.mm"
include "simpr.mm"
include "breq1.mm"
include "elrab.mm"
include "sylib.mm"
include "ffvelrnd.mm"
include "cn0.mm"
include "simplr.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "simprd.mm"
include "psrbagcon.mm"
include "syl13anc.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"
include "fvex.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "ovex.mm"
include "rabex2.mm"
include "elmap.mm"
include "sylibr.mm"
include "psrmulfval.mm"
include "psrbas.mm"
include "3eltr4d.mm"

theorem psrmulcllem
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume psrmulcl.s: |- S = ( I mPwSer R )
  assume psrmulcl.b: |- B = ( Base ` S )
  assume psrmulcl.t: |- .x. = ( .r ` S )
  assume psrmulcl.r: |- ( ph -> R e. Ring )
  assume psrmulcl.x: |- ( ph -> X e. B )
  assume psrmulcl.y: |- ( ph -> Y e. B )
  assume psrmulcl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint I f
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint k ph
  disjoint ph x
  disjoint R k
  disjoint R x
  disjoint X k
  disjoint X x
  disjoint Y k
  disjoint Y x
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint I k
  disjoint I x
  disjoint I y
  assert |- ( ph -> ( X .x. Y ) e. B )

  proof
    wph
    vk
    cD
    cR
    vx
    vy
    cv
    #
    vk
    cv
    #
    cle
    cofr
    #
    wbr
    #
    vy
    cD
    crab
    #
    vx
    cv
    #
    cX
    cfv
    #
    @1
    @5
    cmin
    cof
    co
    #
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
    #
    cR
    cbs
    cfv
    #
    cD
    cmap
    co
    #
    cX
    cY
    c.x
    co
    cB
    wph
    cD
    @14
    @13
    wf
    @13
    @15
    wcel
    wph
    vk
    cD
    @12
    @14
    @13
    wph
    @1
    cD
    wcel
    #
    wa
    #
    @4
    @14
    @11
    cR
    cfn
    cR
    c0g
    cfv
    #
    @14
    eqid
    #
    @18
    eqid
    @17
    cR
    crg
    wcel
    #
    cR
    ccmn
    wcel
    wph
    @20
    @16
    psrmulcl.r
    adantr
    cR
    ringcmn
    syl
    wph
    cI
    cvv
    wcel
    #
    @16
    @4
    cfn
    wcel
    wph
    @21
    cR
    cvv
    wcel
    #
    wph
    cX
    cB
    wcel
    @21
    @22
    wa
    psrmulcl.x
    cX
    cB
    cS
    cmps
    cI
    cR
    reldmpsr
    psrmulcl.s
    psrmulcl.b
    elbasov
    syl
    simpld
    #
    vy
    cD
    vf
    @1
    cI
    cvv
    psrmulcl.d
    psrbaglefi
    sylan
    #
    @17
    vx
    @4
    @10
    @14
    @11
    @17
    @5
    @4
    wcel
    #
    wa
    #
    @20
    @6
    @14
    wcel
    @8
    @14
    wcel
    @10
    @14
    wcel
    wph
    @20
    @16
    @25
    psrmulcl.r
    ad2antrr
    @26
    cD
    @14
    @5
    cX
    wph
    cD
    @14
    cX
    wf
    @16
    @25
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @14
    cX
    psrmulcl.s
    @19
    psrmulcl.d
    psrmulcl.b
    psrmulcl.x
    psrelbas
    ad2antrr
    @26
    @5
    cD
    wcel
    #
    @5
    @1
    @2
    wbr
    #
    @26
    @25
    @27
    @28
    wa
    @17
    @25
    simpr
    @3
    @28
    vy
    @5
    cD
    @0
    @5
    @1
    @2
    breq1
    elrab
    sylib
    #
    simpld
    #
    ffvelrnd
    @26
    cD
    @14
    @7
    cY
    wph
    cD
    @14
    cY
    wf
    @16
    @25
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @14
    cY
    psrmulcl.s
    @19
    psrmulcl.d
    psrmulcl.b
    psrmulcl.y
    psrelbas
    ad2antrr
    @26
    @7
    cD
    wcel
    #
    @7
    @1
    @2
    wbr
    #
    @26
    @21
    @16
    cI
    cn0
    @5
    wf
    #
    @28
    @31
    @32
    wa
    wph
    @21
    @16
    @25
    @23
    ad2antrr
    #
    wph
    @16
    @25
    simplr
    @26
    @21
    @27
    @33
    @34
    @30
    cD
    vf
    @5
    cI
    cvv
    psrmulcl.d
    psrbagf
    syl2anc
    @26
    @27
    @28
    @29
    simprd
    cD
    vf
    @1
    @5
    cI
    cvv
    psrmulcl.d
    psrbagcon
    syl13anc
    simpld
    ffvelrnd
    @14
    cR
    @9
    @6
    @8
    @19
    @9
    eqid
    #
    ringcl
    syl3anc
    @11
    eqid
    fmptd
    #
    @17
    @4
    @14
    @11
    cvv
    @18
    @36
    @24
    @17
    cR
    c0g
    fvexd
    fdmfifsupp
    gsumcl
    @13
    eqid
    fmptd
    @14
    cD
    @13
    cR
    cbs
    fvex
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    psrmulcl.d
    cn0
    cI
    cmap
    ovex
    rabex2
    elmap
    sylibr
    wph
    vx
    vy
    cB
    cD
    cR
    cS
    c.x
    @9
    vf
    vk
    cX
    cY
    cI
    psrmulcl.s
    psrmulcl.b
    @35
    psrmulcl.t
    psrmulcl.d
    psrmulcl.x
    psrmulcl.y
    psrmulfval
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    @14
    cvv
    psrmulcl.s
    @19
    psrmulcl.d
    psrmulcl.b
    @23
    psrbas
    3eltr4d
end
