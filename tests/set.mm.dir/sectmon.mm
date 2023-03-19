include "co.mm"
include "wcel.mm"
include "chom.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "ccid.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "issect.mm"
include "mpbid.mm"
include "simp1d.mm"
include "wa.mm"
include "oveq2.mm"
include "simp3d.mm"
include "ad2antrr.mm"
include "oveq1d.mm"
include "ccat.mm"
include "simplr.mm"
include "simprl.mm"
include "simp2d.mm"
include "catass.mm"
include "catlid.mm"
include "3eqtr3d.mm"
include "simprr.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "ralrimivva.mm"
include "ralrimiva.mm"
include "ismon2.mm"
include "mpbir2and.mm"

theorem sectmon
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  assume sectmon.b: |- B = ( Base ` C )
  assume sectmon.m: |- M = ( Mono ` C )
  assume sectmon.s: |- S = ( Sect ` C )
  assume sectmon.c: |- ( ph -> C e. Cat )
  assume sectmon.x: |- ( ph -> X e. B )
  assume sectmon.y: |- ( ph -> Y e. B )
  assume sectmon.1: |- ( ph -> F ( X S Y ) G )


  assert |- ( ph -> F e. ( X M Y ) )

  proof
    wph
    cF
    cX
    cY
    cM
    co
    wcel
    cF
    cX
    cY
    cC
    chom
    cfv
    #
    co
    wcel
    #
    cF
    vg
    cv
    #
    vx
    cv
    #
    cX
    cop
    #
    cY
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cF
    vh
    cv
    #
    @6
    co
    #
    wceq
    #
    @2
    @8
    wceq
    #
    wi
    #
    vh
    @3
    cX
    @0
    co
    #
    wral
    vg
    @13
    wral
    #
    vx
    cB
    wral
    wph
    @1
    cG
    cY
    cX
    @0
    co
    wcel
    #
    cG
    cF
    cX
    cY
    cop
    cX
    @5
    co
    co
    #
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    wph
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    @1
    @15
    @19
    w3a
    sectmon.1
    wph
    cB
    cC
    cS
    @5
    @17
    cF
    cG
    @0
    cX
    cY
    sectmon.b
    @0
    eqid
    #
    @5
    eqid
    #
    @17
    eqid
    #
    sectmon.s
    sectmon.c
    sectmon.x
    sectmon.y
    issect
    mpbid
    #
    simp1d
    #
    wph
    @14
    vx
    cB
    wph
    @3
    cB
    wcel
    #
    wa
    #
    @12
    vg
    vh
    @13
    @13
    @10
    cG
    @7
    @3
    cY
    cop
    cX
    @5
    co
    #
    co
    #
    cG
    @9
    @27
    co
    #
    wceq
    @26
    @2
    @13
    wcel
    #
    @8
    @13
    wcel
    #
    wa
    #
    wa
    #
    @11
    @7
    @9
    cG
    @27
    oveq2
    @33
    @28
    @2
    @29
    @8
    @33
    @16
    @2
    @4
    cX
    @5
    co
    #
    co
    @18
    @2
    @34
    co
    @28
    @2
    @33
    @16
    @18
    @2
    @34
    wph
    @19
    @25
    @32
    wph
    @1
    @15
    @19
    @23
    simp3d
    ad2antrr
    #
    oveq1d
    @33
    cB
    cC
    @5
    @2
    cF
    @0
    cG
    cX
    @3
    cX
    cY
    sectmon.b
    @20
    @21
    wph
    cC
    ccat
    wcel
    @25
    @32
    sectmon.c
    ad2antrr
    #
    wph
    @25
    @32
    simplr
    #
    wph
    cX
    cB
    wcel
    @25
    @32
    sectmon.x
    ad2antrr
    #
    wph
    cY
    cB
    wcel
    @25
    @32
    sectmon.y
    ad2antrr
    #
    @26
    @30
    @31
    simprl
    #
    wph
    @1
    @25
    @32
    @24
    ad2antrr
    #
    @38
    wph
    @15
    @25
    @32
    wph
    @1
    @15
    @19
    @23
    simp2d
    ad2antrr
    #
    catass
    @33
    cB
    cC
    @5
    @17
    @2
    @0
    @3
    cX
    sectmon.b
    @20
    @22
    @36
    @37
    @21
    @38
    @40
    catlid
    3eqtr3d
    @33
    @16
    @8
    @34
    co
    @18
    @8
    @34
    co
    @29
    @8
    @33
    @16
    @18
    @8
    @34
    @35
    oveq1d
    @33
    cB
    cC
    @5
    @8
    cF
    @0
    cG
    cX
    @3
    cX
    cY
    sectmon.b
    @20
    @21
    @36
    @37
    @38
    @39
    @26
    @30
    @31
    simprr
    #
    @41
    @38
    @42
    catass
    @33
    cB
    cC
    @5
    @17
    @8
    @0
    @3
    cX
    sectmon.b
    @20
    @22
    @36
    @37
    @21
    @38
    @43
    catlid
    3eqtr3d
    eqeq12d
    syl5ib
    ralrimivva
    ralrimiva
    wph
    vx
    cB
    cC
    @5
    vg
    vh
    cF
    @0
    cM
    cX
    cY
    sectmon.b
    @20
    @21
    sectmon.m
    sectmon.c
    sectmon.x
    sectmon.y
    ismon2
    mpbir2and
end
