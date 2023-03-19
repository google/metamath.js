include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cbs.mm"
include "chom.mm"
include "eqid.mm"
include "ccat.mm"
include "cfunc.mm"
include "wbr.mm"
include "cfth.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "simprd.mm"
include "adantr.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "simpr1.mm"
include "funcf2.mm"
include "simpr2.mm"
include "simpr3.mm"
include "moni.mm"
include "funcco.mm"
include "eqeq12d.mm"
include "simpld.mm"
include "catcocl.mm"
include "fthi.mm"
include "bitr3d.mm"
include "3bitr3d.mm"
include "biimpd.mm"
include "ralrimivvva.mm"
include "ismon2.mm"
include "mpbir2and.mm"

theorem fthmon
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cI: class I
  let cJ: class J
  assume fthmon.b: |- B = ( Base ` C )
  assume fthmon.h: |- H = ( Hom ` C )
  assume fthmon.f: |- ( ph -> F ( C Faith D ) G )
  assume fthmon.x: |- ( ph -> X e. B )
  assume fthmon.y: |- ( ph -> Y e. B )
  assume fthmon.r: |- ( ph -> R e. ( X H Y ) )
  assume fthmon.m: |- M = ( Mono ` C )
  assume fthmon.n: |- N = ( Mono ` D )
  assume fthmon.1: |- ( ph -> ( ( X G Y ) ` R ) e. ( ( F ` X ) N ( F ` Y ) ) )


  assert |- ( ph -> R e. ( X M Y ) )

  proof
    wph
    cR
    cX
    cY
    cM
    co
    wcel
    cR
    cX
    cY
    cH
    co
    wcel
    #
    cR
    vf
    cv
    #
    vz
    cv
    #
    cX
    cop
    cY
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cR
    vg
    cv
    #
    @4
    co
    #
    wceq
    #
    @1
    @6
    wceq
    #
    wi
    #
    vg
    @2
    cX
    cH
    co
    #
    wral
    vf
    @11
    wral
    vz
    cB
    wral
    fthmon.r
    wph
    @10
    vz
    vf
    vg
    cB
    @11
    @11
    wph
    @2
    cB
    wcel
    #
    @1
    @11
    wcel
    #
    @6
    @11
    wcel
    #
    w3a
    #
    wa
    #
    @8
    @9
    @16
    cR
    cX
    cY
    cG
    co
    cfv
    #
    @1
    @2
    cX
    cG
    co
    #
    cfv
    #
    @2
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cop
    cY
    cF
    cfv
    #
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    @17
    @6
    @18
    cfv
    #
    @24
    co
    #
    wceq
    #
    @19
    @26
    wceq
    @8
    @9
    @16
    cD
    cbs
    cfv
    #
    cD
    @23
    @17
    @19
    cD
    chom
    cfv
    #
    @26
    cN
    @21
    @22
    @20
    @29
    eqid
    #
    @30
    eqid
    #
    @23
    eqid
    #
    fthmon.n
    wph
    cD
    ccat
    wcel
    #
    @15
    wph
    cC
    ccat
    wcel
    #
    @34
    wph
    cF
    cG
    cop
    #
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    @35
    @34
    wa
    wph
    cF
    cG
    @37
    wbr
    #
    @38
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
    @39
    fthmon.f
    @40
    @37
    cF
    cG
    cC
    cD
    fthfunc
    ssbri
    syl
    #
    cF
    cG
    @37
    df-br
    sylib
    cC
    cD
    @36
    funcrcl
    syl
    #
    simprd
    adantr
    @16
    cB
    @29
    cX
    cF
    @16
    cB
    @29
    cC
    cD
    cF
    cG
    fthmon.b
    @31
    wph
    @39
    @15
    @42
    adantr
    #
    funcf1
    #
    wph
    cX
    cB
    wcel
    @15
    fthmon.x
    adantr
    #
    ffvelrnd
    @16
    cB
    @29
    cY
    cF
    @45
    wph
    cY
    cB
    wcel
    @15
    fthmon.y
    adantr
    #
    ffvelrnd
    @16
    cB
    @29
    @2
    cF
    @45
    wph
    @12
    @13
    @14
    simpr1
    #
    ffvelrnd
    wph
    @17
    @21
    @22
    cN
    co
    wcel
    @15
    fthmon.1
    adantr
    @16
    @11
    @20
    @21
    @30
    co
    #
    @1
    @18
    @16
    cB
    cC
    cD
    cF
    cG
    cH
    @30
    @2
    cX
    fthmon.b
    fthmon.h
    @32
    @44
    @48
    @46
    funcf2
    #
    wph
    @12
    @13
    @14
    simpr2
    #
    ffvelrnd
    @16
    @11
    @49
    @6
    @18
    @50
    wph
    @12
    @13
    @14
    simpr3
    #
    ffvelrnd
    moni
    @16
    @5
    @2
    cY
    cG
    co
    #
    cfv
    #
    @7
    @53
    cfv
    #
    wceq
    @28
    @8
    @16
    @54
    @25
    @55
    @27
    @16
    cB
    cC
    @3
    cD
    cF
    cG
    cH
    @1
    cR
    @23
    @2
    cX
    cY
    fthmon.b
    fthmon.h
    @3
    eqid
    #
    @33
    @44
    @48
    @46
    @47
    @51
    wph
    @0
    @15
    fthmon.r
    adantr
    #
    funcco
    @16
    cB
    cC
    @3
    cD
    cF
    cG
    cH
    @6
    cR
    @23
    @2
    cX
    cY
    fthmon.b
    fthmon.h
    @56
    @33
    @44
    @48
    @46
    @47
    @52
    @57
    funcco
    eqeq12d
    @16
    cB
    cC
    cD
    @5
    @7
    cF
    cG
    cH
    @30
    @2
    cY
    fthmon.b
    fthmon.h
    @32
    wph
    @41
    @15
    fthmon.f
    adantr
    #
    @48
    @47
    @16
    cB
    cC
    @3
    @1
    cR
    cH
    @2
    cX
    cY
    fthmon.b
    fthmon.h
    @56
    wph
    @35
    @15
    wph
    @35
    @34
    @43
    simpld
    #
    adantr
    #
    @48
    @46
    @47
    @51
    @57
    catcocl
    @16
    cB
    cC
    @3
    @6
    cR
    cH
    @2
    cX
    cY
    fthmon.b
    fthmon.h
    @56
    @60
    @48
    @46
    @47
    @52
    @57
    catcocl
    fthi
    bitr3d
    @16
    cB
    cC
    cD
    @1
    @6
    cF
    cG
    cH
    @30
    @2
    cX
    fthmon.b
    fthmon.h
    @32
    @58
    @48
    @46
    @51
    @52
    fthi
    3bitr3d
    biimpd
    ralrimivvva
    wph
    vz
    cB
    cC
    @3
    vf
    vg
    cR
    cH
    cM
    cX
    cY
    fthmon.b
    fthmon.h
    @56
    fthmon.m
    @59
    fthmon.x
    fthmon.y
    ismon2
    mpbir2and
end
