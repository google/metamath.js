include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cfunc.mm"
include "wbr.mm"
include "cfth.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "funciso.mm"
include "cinv.mm"
include "cv.mm"
include "wceq.mm"
include "eqid.mm"
include "ccat.mm"
include "cop.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "simpld.mm"
include "ad3antrrr.mm"
include "cdm.mm"
include "cbs.mm"
include "simprd.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "isoval.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wfun.mm"
include "wb.mm"
include "invfun.mm"
include "funfvbrb.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "breqtrd.mm"
include "simplr.mm"
include "fthinv.mm"
include "mpbird.mm"
include "inviso1.mm"
include "chom.mm"
include "cful.mm"
include "wss.mm"
include "isohom.mm"
include "invf.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "fulli.mm"
include "r19.29a.mm"
include "impbida.mm"

theorem ffthiso
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  assume fthmon.b: |- B = ( Base ` C )
  assume fthmon.h: |- H = ( Hom ` C )
  assume fthmon.f: |- ( ph -> F ( C Faith D ) G )
  assume fthmon.x: |- ( ph -> X e. B )
  assume fthmon.y: |- ( ph -> Y e. B )
  assume fthmon.r: |- ( ph -> R e. ( X H Y ) )
  assume ffthiso.f: |- ( ph -> F ( C Full D ) G )
  assume ffthiso.s: |- I = ( Iso ` C )
  assume ffthiso.t: |- J = ( Iso ` D )


  assert |- ( ph -> ( R e. ( X I Y ) <-> ( ( X G Y ) ` R ) e. ( ( F ` X ) J ( F ` Y ) ) ) )

  proof
    wph
    cR
    cX
    cY
    cI
    co
    wcel
    #
    cR
    cX
    cY
    cG
    co
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cJ
    co
    #
    wcel
    #
    wph
    @0
    wa
    cB
    cC
    cD
    cF
    cG
    cI
    cJ
    cR
    cX
    cY
    fthmon.b
    ffthiso.s
    ffthiso.t
    wph
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    @0
    wph
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    #
    @7
    fthmon.f
    @8
    @6
    cF
    cG
    cC
    cD
    fthfunc
    ssbri
    syl
    #
    adantr
    wph
    cX
    cB
    wcel
    #
    @0
    fthmon.x
    adantr
    wph
    cY
    cB
    wcel
    #
    @0
    fthmon.y
    adantr
    wph
    @0
    simpr
    funciso
    wph
    @5
    wa
    #
    @1
    @2
    @3
    cD
    cinv
    cfv
    #
    co
    #
    cfv
    #
    vf
    cv
    #
    cY
    cX
    cG
    co
    cfv
    #
    wceq
    #
    @0
    vf
    cY
    cX
    cH
    co
    #
    @13
    @17
    @20
    wcel
    #
    wa
    #
    @19
    wa
    #
    cB
    cC
    cR
    @17
    cI
    cC
    cinv
    cfv
    #
    cX
    cY
    fthmon.b
    @24
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    @5
    @21
    @19
    wph
    @26
    cD
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    @6
    wcel
    #
    @26
    @27
    wa
    wph
    @7
    @29
    @10
    cF
    cG
    @6
    df-br
    sylib
    cC
    cD
    @28
    funcrcl
    syl
    #
    simpld
    ad3antrrr
    wph
    @11
    @5
    @21
    @19
    fthmon.x
    ad3antrrr
    #
    wph
    @12
    @5
    @21
    @19
    fthmon.y
    ad3antrrr
    #
    ffthiso.s
    @23
    cR
    @17
    cX
    cY
    @24
    co
    wbr
    @1
    @18
    @15
    wbr
    @23
    @1
    @16
    @18
    @15
    @13
    @1
    @16
    @15
    wbr
    #
    @21
    @19
    @13
    @1
    @15
    cdm
    #
    wcel
    #
    @33
    wph
    @5
    @35
    wph
    @4
    @34
    @1
    wph
    cD
    cbs
    cfv
    #
    cD
    cJ
    @14
    @2
    @3
    @36
    eqid
    #
    @14
    eqid
    #
    wph
    @26
    @27
    @30
    simprd
    #
    wph
    cB
    @36
    cX
    cF
    wph
    cB
    @36
    cC
    cD
    cF
    cG
    fthmon.b
    @37
    @10
    funcf1
    #
    fthmon.x
    ffvelrnd
    #
    wph
    cB
    @36
    cY
    cF
    @40
    fthmon.y
    ffvelrnd
    #
    ffthiso.t
    isoval
    eleq2d
    biimpa
    @13
    @15
    wfun
    #
    @35
    @33
    wb
    wph
    @43
    @5
    wph
    @36
    cD
    @14
    @2
    @3
    @37
    @38
    @39
    @41
    @42
    invfun
    adantr
    @1
    @15
    funfvbrb
    syl
    mpbid
    ad2antrr
    @22
    @19
    simpr
    breqtrd
    @23
    cB
    cC
    cD
    cF
    cG
    cH
    @24
    @14
    cR
    @17
    cX
    cY
    fthmon.b
    fthmon.h
    wph
    @9
    @5
    @21
    @19
    fthmon.f
    ad3antrrr
    @31
    @32
    wph
    cR
    cX
    cY
    cH
    co
    wcel
    @5
    @21
    @19
    fthmon.r
    ad3antrrr
    @13
    @21
    @19
    simplr
    @25
    @38
    fthinv
    mpbird
    inviso1
    @13
    cB
    cC
    cD
    @16
    vf
    cF
    cG
    cH
    cD
    chom
    cfv
    #
    cY
    cX
    fthmon.b
    @44
    eqid
    #
    fthmon.h
    wph
    cF
    cG
    cC
    cD
    cful
    co
    wbr
    @5
    ffthiso.f
    adantr
    wph
    @12
    @5
    fthmon.y
    adantr
    wph
    @11
    @5
    fthmon.x
    adantr
    @13
    @3
    @2
    cJ
    co
    #
    @3
    @2
    @44
    co
    #
    @16
    wph
    @46
    @47
    wss
    @5
    wph
    @36
    cD
    @44
    cJ
    @3
    @2
    @37
    @45
    ffthiso.t
    @39
    @42
    @41
    isohom
    adantr
    wph
    @4
    @46
    @1
    @15
    wph
    @36
    cD
    cJ
    @14
    @2
    @3
    @37
    @38
    @39
    @41
    @42
    ffthiso.t
    invf
    ffvelrnda
    sseldd
    fulli
    r19.29a
    impbida
end
