include "cmnd.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cbs.mm"
include "cv.mm"
include "cmpt.mm"
include "wf.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "prdsmndd.mm"
include "ffvelrnd.mm"
include "jca.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "eqid.mm"
include "fmptd.mm"
include "simprl.mm"
include "simprr.mm"
include "prdsplusgfval.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "fveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ccom.mm"
include "mndidcl.mm"
include "3syl.mm"
include "prds0g.mm"
include "fveq1d.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem prdspjmhm
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume prdspjmhm.y: |- Y = ( S Xs_ R )
  assume prdspjmhm.b: |- B = ( Base ` Y )
  assume prdspjmhm.i: |- ( ph -> I e. V )
  assume prdspjmhm.s: |- ( ph -> S e. X )
  assume prdspjmhm.r: |- ( ph -> R : I --> Mnd )
  assume prdspjmhm.a: |- ( ph -> A e. I )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint R x
  disjoint Y x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint R y
  disjoint R z
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> ( x e. B |-> ( x ` A ) ) e. ( Y MndHom ( R ` A ) ) )

  proof
    wph
    cY
    cmnd
    wcel
    #
    cA
    cR
    cfv
    #
    cmnd
    wcel
    #
    wa
    cB
    @1
    cbs
    cfv
    #
    vx
    cB
    cA
    vx
    cv
    #
    cfv
    #
    cmpt
    #
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    @6
    cfv
    #
    @8
    @6
    cfv
    #
    @9
    @6
    cfv
    #
    @1
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    cY
    c0g
    cfv
    #
    @6
    cfv
    #
    @1
    c0g
    cfv
    #
    wceq
    #
    w3a
    @6
    cY
    @1
    cmhm
    co
    wcel
    wph
    @0
    @2
    wph
    cR
    cS
    cI
    cX
    cV
    cY
    prdspjmhm.y
    prdspjmhm.i
    prdspjmhm.s
    prdspjmhm.r
    prdsmndd
    #
    wph
    cI
    cmnd
    cA
    cR
    prdspjmhm.r
    prdspjmhm.a
    ffvelrnd
    jca
    wph
    @7
    @18
    @22
    wph
    vx
    cB
    @5
    @3
    @6
    wph
    @4
    cB
    wcel
    #
    wa
    cB
    cR
    cS
    @4
    cI
    cA
    cX
    cV
    cY
    prdspjmhm.y
    prdspjmhm.b
    wph
    cS
    cX
    wcel
    #
    @24
    prdspjmhm.s
    adantr
    wph
    cI
    cV
    wcel
    #
    @24
    prdspjmhm.i
    adantr
    wph
    cR
    cI
    wfn
    #
    @24
    wph
    cI
    cmnd
    cR
    wf
    #
    @27
    prdspjmhm.r
    cI
    cmnd
    cR
    ffn
    syl
    #
    adantr
    wph
    @24
    simpr
    wph
    cA
    cI
    wcel
    #
    @24
    prdspjmhm.a
    adantr
    prdsbasprj
    @6
    eqid
    #
    fmptd
    wph
    @17
    vy
    vz
    cB
    cB
    wph
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    wa
    #
    wa
    #
    cA
    @11
    cfv
    #
    cA
    @8
    cfv
    #
    cA
    @9
    cfv
    #
    @15
    co
    #
    @12
    @16
    @35
    cB
    @10
    cR
    cS
    @8
    @9
    cI
    cA
    cX
    cV
    cY
    prdspjmhm.y
    prdspjmhm.b
    wph
    @25
    @34
    prdspjmhm.s
    adantr
    wph
    @26
    @34
    prdspjmhm.i
    adantr
    wph
    @27
    @34
    @29
    adantr
    wph
    @32
    @33
    simprl
    wph
    @32
    @33
    simprr
    @10
    eqid
    #
    wph
    @30
    @34
    prdspjmhm.a
    adantr
    prdsplusgfval
    @35
    @11
    cB
    wcel
    #
    @12
    @36
    wceq
    wph
    @0
    @34
    @41
    @23
    @0
    @32
    @33
    @41
    cB
    @10
    cY
    @8
    @9
    prdspjmhm.b
    @40
    mndcl
    3expb
    sylan
    vx
    @11
    @5
    @36
    cB
    @6
    cA
    @4
    @11
    fveq1
    @31
    cA
    @11
    fvex
    fvmpt
    syl
    @34
    @16
    @39
    wceq
    wph
    @32
    @33
    @13
    @37
    @14
    @38
    @15
    vx
    @8
    @5
    @37
    cB
    @6
    cA
    @4
    @8
    fveq1
    @31
    cA
    @8
    fvex
    fvmpt
    vx
    @9
    @5
    @38
    cB
    @6
    cA
    @4
    @9
    fveq1
    @31
    cA
    @9
    fvex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    wph
    @20
    cA
    @19
    cfv
    #
    cA
    c0g
    cR
    ccom
    #
    cfv
    #
    @21
    wph
    @0
    @19
    cB
    wcel
    @20
    @42
    wceq
    @23
    cB
    cY
    @19
    prdspjmhm.b
    @19
    eqid
    #
    mndidcl
    vx
    @19
    @5
    @42
    cB
    @6
    cA
    @4
    @19
    fveq1
    @31
    cA
    @19
    fvex
    fvmpt
    3syl
    wph
    cA
    @43
    @19
    wph
    cR
    cS
    cI
    cX
    cV
    cY
    prdspjmhm.y
    prdspjmhm.i
    prdspjmhm.s
    prdspjmhm.r
    prds0g
    fveq1d
    wph
    @28
    @30
    @44
    @21
    wceq
    prdspjmhm.r
    prdspjmhm.a
    cI
    cmnd
    cA
    c0g
    cR
    fvco3
    syl2anc
    3eqtr2d
    3jca
    vy
    vz
    cB
    @3
    @10
    @15
    cY
    @1
    @6
    @21
    @19
    prdspjmhm.b
    @3
    eqid
    @40
    @15
    eqid
    @45
    @21
    eqid
    ismhm
    sylanbrc
end
