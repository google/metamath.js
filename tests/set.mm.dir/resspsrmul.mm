include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cmin.mm"
include "cof.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "elbasov.mm"
include "ad2antrl.mm"
include "simpld.mm"
include "eqid.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "csubmnd.mm"
include "csubg.mm"
include "csubrg.mm"
include "subrgsubg.mm"
include "syl.mm"
include "subgsubm.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "cbs.mm"
include "wf.mm"
include "simprl.mm"
include "psrelbas.mm"
include "adantr.mm"
include "elrabi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "wceq.mm"
include "subrgbas.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "ssrab2.mm"
include "simplr.mm"
include "simpr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "subrgmcl.mm"
include "fmptd.mm"
include "gsumsubm.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wss.mm"
include "fvex.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "mapss.mm"
include "sylancr.mm"
include "psrbas.mm"
include "3sstr4d.mm"
include "sseldd.mm"
include "psrmulfval.mm"
include "3eqtr4rd.mm"
include "eqeltri.mm"
include "mp1i.mm"

theorem resspsrmul
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vf: setvar f
  let vy: setvar y
  assume resspsr.s: |- S = ( I mPwSer R )
  assume resspsr.h: |- H = ( R |`s T )
  assume resspsr.u: |- U = ( I mPwSer H )
  assume resspsr.b: |- B = ( Base ` U )
  assume resspsr.p: |- P = ( S |`s B )
  assume resspsr.2: |- ( ph -> T e. ( SubRing ` R ) )


  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X ( .r ` U ) Y ) = ( X ( .r ` P ) Y ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cU
    cmulr
    cfv
    #
    co
    #
    cX
    cY
    cS
    cmulr
    cfv
    #
    co
    #
    cX
    cY
    cP
    cmulr
    cfv
    #
    co
    @3
    vk
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
    crab
    #
    cR
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    #
    vy
    @9
    crab
    #
    vx
    cv
    #
    cX
    cfv
    #
    @10
    @13
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
    vk
    @9
    cH
    vx
    @12
    @14
    @16
    cH
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
    @7
    @5
    @3
    vk
    @9
    @20
    @24
    @3
    @10
    @9
    wcel
    #
    wa
    #
    @20
    cH
    @19
    cgsu
    co
    @24
    @26
    @12
    cT
    @19
    cR
    cH
    cfn
    @3
    cI
    cvv
    wcel
    #
    @25
    @12
    cfn
    wcel
    @3
    @27
    cH
    cvv
    wcel
    #
    @0
    @27
    @28
    wa
    wph
    @1
    cX
    cB
    cU
    cmps
    cI
    cH
    reldmpsr
    resspsr.u
    resspsr.b
    elbasov
    ad2antrl
    simpld
    #
    vy
    @9
    vf
    @10
    cI
    cvv
    @9
    eqid
    #
    psrbaglefi
    sylan
    wph
    cT
    cR
    csubmnd
    cfv
    wcel
    #
    @2
    @25
    wph
    cT
    cR
    csubg
    cfv
    wcel
    #
    @31
    wph
    cT
    cR
    csubrg
    cfv
    #
    wcel
    #
    @32
    resspsr.2
    cT
    cR
    subrgsubg
    syl
    cT
    cR
    subgsubm
    syl
    ad2antrr
    @26
    vx
    @12
    @18
    cT
    @19
    @26
    @13
    @12
    wcel
    #
    wa
    #
    @34
    @14
    cT
    wcel
    @16
    cT
    wcel
    @18
    cT
    wcel
    wph
    @34
    @2
    @25
    @35
    resspsr.2
    ad3antrrr
    #
    @36
    @14
    cH
    cbs
    cfv
    #
    cT
    @26
    @9
    @38
    cX
    wf
    #
    @13
    @9
    wcel
    @14
    @38
    wcel
    @35
    @3
    @39
    @25
    @3
    cB
    @9
    cH
    cU
    vf
    cI
    @38
    cX
    resspsr.u
    @38
    eqid
    #
    @30
    resspsr.b
    wph
    @0
    @1
    simprl
    #
    psrelbas
    adantr
    @11
    vy
    @13
    @9
    elrabi
    @9
    @38
    @13
    cX
    ffvelrn
    syl2an
    @36
    @34
    cT
    @38
    wceq
    #
    @37
    cT
    cR
    cH
    resspsr.h
    subrgbas
    #
    syl
    #
    eleqtrrd
    @36
    @16
    @38
    cT
    @36
    @9
    @38
    @15
    cY
    @3
    @9
    @38
    cY
    wf
    @25
    @35
    @3
    cB
    @9
    cH
    cU
    vf
    cI
    @38
    cY
    resspsr.u
    @40
    @30
    resspsr.b
    wph
    @0
    @1
    simprr
    #
    psrelbas
    ad2antrr
    @36
    @12
    @9
    @15
    @11
    vy
    @9
    ssrab2
    @36
    @27
    @25
    @35
    @15
    @12
    wcel
    @3
    @27
    @25
    @35
    @29
    ad2antrr
    @3
    @25
    @35
    simplr
    @26
    @35
    simpr
    vy
    @9
    @12
    vf
    @10
    cI
    cvv
    @13
    @30
    @12
    eqid
    psrbagconcl
    syl3anc
    sseldi
    ffvelrnd
    @44
    eleqtrrd
    cT
    cR
    @17
    @14
    @16
    @17
    eqid
    #
    subrgmcl
    syl3anc
    @19
    eqid
    fmptd
    resspsr.h
    gsumsubm
    @26
    @19
    @23
    cH
    cgsu
    @26
    vx
    @12
    @18
    @22
    @36
    @17
    @21
    @14
    @16
    wph
    @17
    @21
    wceq
    #
    @2
    @25
    @35
    wph
    @34
    @47
    resspsr.2
    cT
    cR
    cH
    @17
    @33
    resspsr.h
    @46
    ressmulr
    syl
    ad3antrrr
    oveqd
    mpteq2dva
    oveq2d
    eqtrd
    mpteq2dva
    @3
    vx
    vy
    cS
    cbs
    cfv
    #
    @9
    cR
    cS
    @6
    @17
    vf
    vk
    cX
    cY
    cI
    resspsr.s
    @48
    eqid
    #
    @46
    @6
    eqid
    #
    @30
    @3
    cB
    @48
    cX
    @3
    @38
    @9
    cmap
    co
    #
    cR
    cbs
    cfv
    #
    @9
    cmap
    co
    #
    cB
    @48
    wph
    @51
    @53
    wss
    #
    @2
    wph
    @52
    cvv
    wcel
    @38
    @52
    wss
    @54
    cR
    cbs
    fvex
    wph
    @38
    cT
    @52
    wph
    @34
    @42
    resspsr.2
    @43
    syl
    wph
    @34
    cT
    @52
    wss
    resspsr.2
    cT
    @52
    cR
    @52
    eqid
    #
    subrgss
    syl
    eqsstr3d
    @38
    @52
    @9
    cvv
    mapss
    sylancr
    adantr
    @3
    cB
    @9
    cH
    cU
    vf
    cI
    @38
    cvv
    resspsr.u
    @40
    @30
    resspsr.b
    @29
    psrbas
    @3
    @48
    @9
    cR
    cS
    vf
    cI
    @52
    cvv
    resspsr.s
    @55
    @30
    @49
    @29
    psrbas
    3sstr4d
    #
    @41
    sseldd
    @3
    cB
    @48
    cY
    @56
    @45
    sseldd
    psrmulfval
    @3
    vx
    vy
    cB
    @9
    cH
    cU
    @4
    @21
    vf
    vk
    cX
    cY
    cI
    resspsr.u
    resspsr.b
    @21
    eqid
    @4
    eqid
    @30
    @41
    @45
    psrmulfval
    3eqtr4rd
    @3
    @6
    @8
    cX
    cY
    cB
    cvv
    wcel
    @6
    @8
    wceq
    @3
    cB
    cU
    cbs
    cfv
    cvv
    resspsr.b
    cU
    cbs
    fvex
    eqeltri
    cB
    cS
    cP
    @6
    cvv
    resspsr.p
    @50
    ressmulr
    mp1i
    oveqd
    eqtrd
end
