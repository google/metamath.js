include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "cress.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "frlmpws.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "ovexd.mm"
include "clss.mm"
include "wss.mm"
include "frlmlss.mm"
include "lssss.mm"
include "syl.mm"
include "fmptd.mm"
include "clmod.mm"
include "rlmlmod.mm"
include "pwslmod.mm"
include "lss0cl.mm"
include "cmnd.mm"
include "cv.mm"
include "wa.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "cmnmnd.mm"
include "pwsmnd.mm"
include "mndlrid.mm"
include "sylan.mm"
include "gsumress.mm"
include "rlmbas.mm"
include "wf.mm"
include "wral.mm"
include "adantr.mm"
include "frlmbasf.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "anasss.mm"
include "cfsupp.mm"
include "fveq2d.mm"
include "csubg.mm"
include "lsssubg.mm"
include "subg0.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "pwsgsum.mm"
include "mptexg.mm"
include "fvexd.mm"
include "a1i.mm"
include "rlmplusg.mm"
include "gsumpropd.mm"
include "mpteq2dv.mm"
include "3eqtr2d.mm"

theorem frlmgsum
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  assume frlmgsum.y: |- Y = ( R freeLMod I )
  assume frlmgsum.b: |- B = ( Base ` Y )
  assume frlmgsum.z: |- .0. = ( 0g ` Y )
  assume frlmgsum.i: |- ( ph -> I e. V )
  assume frlmgsum.j: |- ( ph -> J e. W )
  assume frlmgsum.r: |- ( ph -> R e. Ring )
  assume frlmgsum.f: |- ( ( ph /\ y e. J ) -> ( x e. I |-> U ) e. B )
  assume frlmgsum.w: |- ( ph -> ( y e. J |-> ( x e. I |-> U ) ) finSupp .0. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint I x
  disjoint I y
  disjoint ph x
  disjoint ph y
  disjoint .0. x
  disjoint .0. y
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( Y gsum ( y e. J |-> ( x e. I |-> U ) ) ) = ( x e. I |-> ( R gsum ( y e. J |-> U ) ) ) )

  proof
    wph
    cY
    vy
    cJ
    vx
    cI
    cU
    cmpt
    #
    cmpt
    #
    cgsu
    co
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    cB
    cress
    co
    #
    @1
    cgsu
    co
    @3
    @1
    cgsu
    co
    #
    vx
    cI
    cR
    vy
    cJ
    cU
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    wph
    cY
    @4
    @1
    cgsu
    wph
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    cY
    @4
    wceq
    frlmgsum.r
    frlmgsum.i
    cB
    cR
    cY
    cI
    crg
    cV
    frlmgsum.y
    frlmgsum.b
    frlmpws
    syl2anc
    #
    oveq1d
    wph
    vx
    cJ
    @3
    cbs
    cfv
    #
    @3
    cplusg
    cfv
    #
    cB
    @1
    @3
    @4
    cvv
    cW
    @3
    c0g
    cfv
    #
    @12
    eqid
    #
    @13
    eqid
    #
    @4
    eqid
    #
    wph
    @2
    cI
    cpws
    ovexd
    frlmgsum.j
    wph
    cB
    @3
    clss
    cfv
    #
    wcel
    #
    cB
    @12
    wss
    wph
    @9
    @10
    @19
    frlmgsum.r
    frlmgsum.i
    cB
    cR
    @18
    cY
    cI
    cV
    frlmgsum.y
    frlmgsum.b
    @18
    eqid
    #
    frlmlss
    syl2anc
    #
    @18
    cB
    @12
    @3
    @15
    @20
    lssss
    syl
    wph
    vy
    cJ
    @0
    cB
    @1
    frlmgsum.f
    @1
    eqid
    fmptd
    wph
    @3
    clmod
    wcel
    #
    @19
    @14
    cB
    wcel
    wph
    @2
    clmod
    wcel
    #
    @10
    @22
    wph
    @9
    @23
    frlmgsum.r
    cR
    rlmlmod
    syl
    #
    frlmgsum.i
    @2
    cI
    cV
    @3
    @3
    eqid
    #
    pwslmod
    syl2anc
    #
    @21
    @18
    cB
    @3
    @14
    @14
    eqid
    #
    @20
    lss0cl
    syl2anc
    wph
    @3
    cmnd
    wcel
    #
    vx
    cv
    #
    @12
    wcel
    @14
    @29
    @13
    co
    @29
    wceq
    @29
    @14
    @13
    co
    @29
    wceq
    wa
    wph
    @2
    cmnd
    wcel
    #
    @10
    @28
    wph
    @2
    ccmn
    wcel
    #
    @30
    wph
    @23
    @31
    @24
    @2
    lmodcmn
    syl
    #
    @2
    cmnmnd
    syl
    frlmgsum.i
    @2
    cI
    cV
    @3
    @25
    pwsmnd
    syl2anc
    @12
    @13
    @3
    @29
    @14
    @15
    @16
    @27
    mndlrid
    sylan
    gsumress
    wph
    @5
    vx
    cI
    @2
    @6
    cgsu
    co
    #
    cmpt
    @8
    wph
    vx
    vy
    cR
    cbs
    cfv
    #
    @2
    cU
    cI
    cJ
    cV
    cW
    @3
    @14
    @25
    cR
    rlmbas
    #
    @27
    frlmgsum.i
    frlmgsum.j
    @32
    wph
    @29
    cI
    wcel
    #
    vy
    cv
    cJ
    wcel
    #
    cU
    @34
    wcel
    #
    wph
    @37
    @36
    @38
    wph
    @37
    wa
    #
    @38
    vx
    cI
    @39
    cI
    @34
    @0
    wf
    #
    @38
    vx
    cI
    wral
    @39
    @10
    @0
    cB
    wcel
    @40
    wph
    @10
    @37
    frlmgsum.i
    adantr
    frlmgsum.f
    cB
    cR
    cY
    cI
    @34
    cV
    @0
    frlmgsum.y
    @34
    eqid
    frlmgsum.b
    frlmbasf
    syl2anc
    vx
    cI
    @34
    cU
    @0
    @0
    eqid
    fmpt
    sylibr
    r19.21bi
    an32s
    anasss
    wph
    @1
    c.0
    @14
    cfsupp
    frlmgsum.w
    wph
    c.0
    cY
    c0g
    cfv
    #
    @14
    frlmgsum.z
    wph
    @41
    @4
    c0g
    cfv
    #
    @14
    wph
    cY
    @4
    c0g
    @11
    fveq2d
    wph
    cB
    @3
    csubg
    cfv
    wcel
    #
    @14
    @42
    wceq
    wph
    @22
    @19
    @43
    @26
    @21
    @18
    cB
    @3
    @20
    lsssubg
    syl2anc
    cB
    @3
    @4
    @14
    @17
    @27
    subg0
    syl
    eqtr4d
    syl5eq
    breqtrd
    pwsgsum
    wph
    vx
    cI
    @7
    @33
    wph
    @6
    cR
    @2
    cvv
    crg
    cvv
    wph
    cJ
    cW
    wcel
    @6
    cvv
    wcel
    frlmgsum.j
    vy
    cJ
    cU
    cW
    mptexg
    syl
    frlmgsum.r
    wph
    cR
    crglmod
    fvexd
    @34
    @2
    cbs
    cfv
    wceq
    wph
    @35
    a1i
    cR
    cplusg
    cfv
    @2
    cplusg
    cfv
    wceq
    wph
    cR
    rlmplusg
    a1i
    gsumpropd
    mpteq2dv
    eqtr4d
    3eqtr2d
end
