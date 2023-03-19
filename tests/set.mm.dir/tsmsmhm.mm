include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cmpt.mm"
include "ccom.mm"
include "wss.mm"
include "crab.mm"
include "crn.mm"
include "cfg.mm"
include "cflf.mm"
include "ctsu.mm"
include "ctopon.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "ccnp.mm"
include "ctps.mm"
include "istps.mm"
include "sylib.mm"
include "cfbas.mm"
include "eqid.mm"
include "tsmsfbas.mm"
include "fgcl.mm"
include "syl.mm"
include "tsmslem1.mm"
include "fmptd.mm"
include "tsmsval.mm"
include "eleqtrd.mm"
include "ccn.mm"
include "cuni.mm"
include "tsmscl.mm"
include "sseldd.mm"
include "wceq.mm"
include "toponuni.mm"
include "cncnpi.mm"
include "syl2anc.mm"
include "flfcnp.mm"
include "syl32anc.mm"
include "cbs.mm"
include "ccmn.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fco.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "wa.mm"
include "resco.mm"
include "oveq2i.mm"
include "c0g.mm"
include "adantr.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "elfpw.mm"
include "simprbi.mm"
include "adantl.mm"
include "cmhm.mm"
include "simplbi.mm"
include "fssres.mm"
include "syl2an.mm"
include "cvv.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "gsummhm.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"

theorem tsmsmhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume tsmsmhm.b: |- B = ( Base ` G )
  assume tsmsmhm.j: |- J = ( TopOpen ` G )
  assume tsmsmhm.k: |- K = ( TopOpen ` H )
  assume tsmsmhm.1: |- ( ph -> G e. CMnd )
  assume tsmsmhm.2: |- ( ph -> G e. TopSp )
  assume tsmsmhm.3: |- ( ph -> H e. CMnd )
  assume tsmsmhm.4: |- ( ph -> H e. TopSp )
  assume tsmsmhm.5: |- ( ph -> C e. ( G MndHom H ) )
  assume tsmsmhm.6: |- ( ph -> C e. ( J Cn K ) )
  assume tsmsmhm.a: |- ( ph -> A e. V )
  assume tsmsmhm.f: |- ( ph -> F : A --> B )
  assume tsmsmhm.x: |- ( ph -> X e. ( G tsums F ) )


  assert |- ( ph -> ( C ` X ) e. ( H tsums ( C o. F ) ) )

  proof
    wph
    cX
    cC
    cfv
    #
    cC
    vz
    cA
    cpw
    cfn
    cin
    #
    cG
    cF
    vz
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    ccom
    #
    cK
    @1
    vy
    @1
    vy
    cv
    @2
    wss
    vz
    @1
    crab
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cflf
    co
    #
    cfv
    #
    cH
    cC
    cF
    ccom
    #
    ctsu
    co
    #
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @9
    @1
    cfil
    cfv
    wcel
    #
    @1
    cB
    @5
    wf
    cX
    @5
    cJ
    @9
    cflf
    co
    cfv
    #
    wcel
    cC
    cX
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    @0
    @11
    wcel
    wph
    cG
    ctps
    wcel
    @14
    tsmsmhm.2
    cB
    cJ
    cG
    tsmsmhm.b
    tsmsmhm.j
    istps
    sylib
    #
    wph
    @8
    @1
    cfbas
    cfv
    wcel
    @15
    wph
    vz
    vy
    cA
    @1
    @7
    @8
    cV
    @1
    eqid
    #
    @7
    eqid
    @8
    eqid
    #
    tsmsmhm.a
    tsmsfbas
    @8
    @1
    fgcl
    syl
    wph
    vz
    @1
    @4
    cB
    @5
    wph
    cA
    cB
    @1
    cF
    cG
    cV
    @2
    tsmsmhm.b
    @19
    tsmsmhm.1
    tsmsmhm.a
    tsmsmhm.f
    tsmslem1
    #
    @5
    eqid
    fmptd
    wph
    cX
    cG
    cF
    ctsu
    co
    #
    @16
    tsmsmhm.x
    wph
    vz
    vy
    cA
    cB
    @1
    cF
    cG
    cJ
    @8
    ctps
    cV
    tsmsmhm.b
    tsmsmhm.j
    @19
    @20
    tsmsmhm.2
    tsmsmhm.a
    tsmsmhm.f
    tsmsval
    eleqtrd
    wph
    cC
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cJ
    cuni
    #
    wcel
    @17
    tsmsmhm.6
    wph
    cX
    cB
    @24
    wph
    @22
    cB
    cX
    wph
    cA
    cB
    cF
    cG
    cV
    tsmsmhm.b
    tsmsmhm.1
    tsmsmhm.2
    tsmsmhm.a
    tsmsmhm.f
    tsmscl
    tsmsmhm.x
    sseldd
    wph
    @14
    cB
    @24
    wceq
    @18
    cB
    cJ
    toponuni
    syl
    eleqtrd
    cX
    cC
    cJ
    cK
    @24
    @24
    eqid
    cncnpi
    syl2anc
    cX
    @5
    cC
    cJ
    cK
    @9
    cB
    @1
    flfcnp
    syl32anc
    wph
    @13
    vz
    @1
    cH
    @12
    @2
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    @10
    cfv
    @11
    wph
    vz
    vy
    cA
    cH
    cbs
    cfv
    #
    @1
    @12
    cH
    cK
    @8
    ccmn
    cV
    @28
    eqid
    #
    tsmsmhm.k
    @19
    @20
    tsmsmhm.3
    tsmsmhm.a
    wph
    cB
    @28
    cC
    wf
    #
    cA
    cB
    cF
    wf
    #
    cA
    @28
    @12
    wf
    wph
    @14
    cK
    @28
    ctopon
    cfv
    wcel
    #
    @23
    @30
    @18
    wph
    cH
    ctps
    wcel
    @32
    tsmsmhm.4
    @28
    cK
    cH
    @29
    tsmsmhm.k
    istps
    sylib
    tsmsmhm.6
    cC
    cJ
    cK
    cB
    @28
    cnf2
    syl3anc
    #
    tsmsmhm.f
    cA
    cB
    @28
    cC
    cF
    fco
    syl2anc
    tsmsval
    wph
    @6
    @27
    @10
    wph
    @6
    vz
    @1
    @4
    cC
    cfv
    #
    cmpt
    @27
    wph
    vz
    vw
    @1
    cB
    @4
    vw
    cv
    #
    cC
    cfv
    @34
    @5
    cC
    @21
    wph
    @5
    eqidd
    wph
    vw
    cB
    @28
    cC
    @33
    feqmptd
    @35
    @4
    cC
    fveq2
    fmptco
    wph
    vz
    @1
    @26
    @34
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @26
    cH
    cC
    @3
    ccom
    #
    cgsu
    co
    @34
    @25
    @38
    cH
    cgsu
    cC
    cF
    @2
    resco
    oveq2i
    @37
    @2
    cB
    @3
    cG
    cH
    cC
    cfn
    cG
    c0g
    cfv
    #
    tsmsmhm.b
    @39
    eqid
    wph
    cG
    ccmn
    wcel
    @36
    tsmsmhm.1
    adantr
    @37
    cH
    ccmn
    wcel
    #
    cH
    cmnd
    wcel
    wph
    @40
    @36
    tsmsmhm.3
    adantr
    cH
    cmnmnd
    syl
    @36
    @2
    cfn
    wcel
    #
    wph
    @36
    @2
    cA
    wss
    #
    @41
    @2
    cA
    elfpw
    #
    simprbi
    adantl
    #
    wph
    cC
    cG
    cH
    cmhm
    co
    wcel
    @36
    tsmsmhm.5
    adantr
    wph
    @31
    @42
    @2
    cB
    @3
    wf
    @36
    tsmsmhm.f
    @36
    @42
    @41
    @43
    simplbi
    cA
    cB
    @2
    cF
    fssres
    syl2an
    #
    @37
    @2
    cB
    @3
    cvv
    @39
    @45
    @44
    @37
    cG
    c0g
    fvexd
    fdmfifsupp
    gsummhm
    syl5eq
    mpteq2dva
    eqtr4d
    fveq2d
    eqtr4d
    eleqtrrd
end
