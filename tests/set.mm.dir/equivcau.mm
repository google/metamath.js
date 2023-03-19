include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cbl.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cc.mm"
include "cpm.mm"
include "crab.mm"
include "cca.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "wi.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "rpdivcld.mm"
include "wceq.mm"
include "oveq2.mm"
include "feq3d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "simprr.mm"
include "wss.mm"
include "cdm.mm"
include "elpmi.mm"
include "simpld.mm"
include "ad3antlr.mm"
include "resss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "uzid.mm"
include "ad2antrl.mm"
include "fdm.mm"
include "ad2antll.mm"
include "eleqtrrd.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "cmopn.mm"
include "eqid.mm"
include "metss2lem.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "imbi2d.mm"
include "syl3c.mm"
include "fssd.mm"
include "reximdva.mm"
include "syld.mm"
include "ralrimdva.mm"
include "ss2rabdv.mm"
include "cme.mm"
include "cxmt.mm"
include "metxmet.mm"
include "caufval.mm"
include "3syl.mm"
include "3sstr4d.mm"

theorem equivcau
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vs: setvar s
  assume equivcau.1: |- ( ph -> C e. ( Met ` X ) )
  assume equivcau.2: |- ( ph -> D e. ( Met ` X ) )
  assume equivcau.3: |- ( ph -> R e. RR+ )
  assume equivcau.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x C y ) <_ ( R x. ( x D y ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint f k
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint C k
  disjoint r x
  disjoint r y
  disjoint C r
  disjoint f s
  disjoint D f
  disjoint k s
  disjoint D k
  disjoint r s
  disjoint D r
  disjoint s x
  disjoint s y
  disjoint D s
  disjoint f ph
  disjoint k ph
  disjoint ph r
  disjoint R k
  disjoint R s
  disjoint X f
  disjoint X k
  disjoint X r
  disjoint X s
  assert |- ( ph -> ( Cau ` D ) C_ ( Cau ` C ) )

  proof
    wph
    vk
    cv
    #
    cuz
    cfv
    #
    @0
    vf
    cv
    #
    cfv
    #
    vs
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @2
    @1
    cres
    #
    wf
    #
    vk
    cz
    wrex
    #
    vs
    crp
    wral
    #
    vf
    cX
    cc
    cpm
    co
    #
    crab
    #
    @1
    @3
    vr
    cv
    #
    cC
    cbl
    cfv
    #
    co
    #
    @7
    wf
    #
    vk
    cz
    wrex
    #
    vr
    crp
    wral
    #
    vf
    @11
    crab
    #
    cD
    cca
    cfv
    #
    cC
    cca
    cfv
    #
    wph
    @10
    @18
    vf
    @11
    wph
    @2
    @11
    wcel
    #
    wa
    #
    @10
    @17
    vr
    crp
    @23
    @13
    crp
    wcel
    #
    wa
    #
    @10
    @1
    @3
    @13
    cR
    cdiv
    co
    #
    @5
    co
    #
    @7
    wf
    #
    vk
    cz
    wrex
    #
    @17
    @25
    @26
    crp
    wcel
    @10
    @29
    wi
    @25
    @13
    cR
    @23
    @24
    simpr
    wph
    cR
    crp
    wcel
    @22
    @24
    equivcau.3
    ad2antrr
    rpdivcld
    @9
    @29
    vs
    @26
    crp
    @4
    @26
    wceq
    #
    @8
    @28
    vk
    cz
    @30
    @6
    @27
    @7
    @1
    @4
    @26
    @3
    @5
    oveq2
    feq3d
    rexbidv
    rspcv
    syl
    @25
    @28
    @16
    vk
    cz
    @25
    @0
    cz
    wcel
    #
    @28
    @16
    @25
    @31
    @28
    wa
    #
    wa
    #
    @1
    @27
    @15
    @7
    @25
    @31
    @28
    simprr
    @33
    @3
    cX
    wcel
    @24
    vx
    cv
    #
    @26
    @5
    co
    #
    @34
    @13
    @14
    co
    #
    wss
    #
    wi
    #
    vx
    cX
    wral
    #
    @24
    @27
    @15
    wss
    #
    @33
    @2
    cdm
    #
    cX
    @0
    @2
    @22
    @41
    cX
    @2
    wf
    #
    wph
    @24
    @32
    @22
    @42
    @41
    cc
    wss
    cX
    cc
    @2
    elpmi
    simpld
    ad3antlr
    @33
    @7
    cdm
    #
    @41
    @0
    @7
    @2
    wss
    @43
    @41
    wss
    @2
    @1
    resss
    @7
    @2
    dmss
    ax-mp
    @33
    @0
    @1
    @43
    @31
    @0
    @1
    wcel
    @25
    @28
    @0
    uzid
    ad2antrl
    @28
    @43
    @1
    wceq
    @25
    @31
    @1
    @27
    @7
    fdm
    ad2antll
    eleqtrrd
    sseldi
    ffvelrnd
    wph
    @39
    @22
    @24
    @32
    wph
    @38
    vx
    cX
    wph
    @34
    cX
    wcel
    @24
    @37
    wph
    vx
    vy
    cC
    cD
    cR
    @13
    cC
    cmopn
    cfv
    #
    cD
    cmopn
    cfv
    #
    cX
    @44
    eqid
    @45
    eqid
    equivcau.1
    equivcau.2
    equivcau.3
    equivcau.4
    metss2lem
    expr
    ralrimiva
    ad3antrrr
    @23
    @24
    @32
    simplr
    @38
    @24
    @40
    wi
    vx
    @3
    cX
    @34
    @3
    wceq
    #
    @37
    @40
    @24
    @46
    @35
    @27
    @36
    @15
    @34
    @3
    @26
    @5
    oveq1
    @34
    @3
    @13
    @14
    oveq1
    sseq12d
    imbi2d
    rspcv
    syl3c
    fssd
    expr
    reximdva
    syld
    ralrimdva
    ss2rabdv
    wph
    cD
    cX
    cme
    cfv
    #
    wcel
    cD
    cX
    cxmt
    cfv
    #
    wcel
    @20
    @12
    wceq
    equivcau.2
    cD
    cX
    metxmet
    vs
    cD
    vf
    vk
    cX
    caufval
    3syl
    wph
    cC
    @47
    wcel
    cC
    @48
    wcel
    @21
    @19
    wceq
    equivcau.1
    cC
    cX
    metxmet
    vr
    cC
    vf
    vk
    cX
    caufval
    3syl
    3sstr4d
end
