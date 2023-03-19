include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "chom.mm"
include "cixp.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "cfunc.mm"
include "wbr.mm"
include "natrcl.mm"
include "syl.mm"
include "simpld.mm"
include "df-br.mm"
include "sylibr.mm"
include "simprd.mm"
include "isnat.mm"
include "mpbid.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "simpllr.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "fveq12d.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "mpd.mm"

theorem nati
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let cJ: class J
  assume natrcl.1: |- N = ( C Nat D )
  assume natixp.2: |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) )
  assume natixp.b: |- B = ( Base ` C )
  assume nati.h: |- H = ( Hom ` C )
  assume nati.o: |- .x. = ( comp ` D )
  assume nati.x: |- ( ph -> X e. B )
  assume nati.y: |- ( ph -> Y e. B )
  assume nati.r: |- ( ph -> R e. ( X H Y ) )


  assert |- ( ph -> ( ( A ` Y ) ( <. ( F ` X ) , ( F ` Y ) >. .x. ( K ` Y ) ) ( ( X G Y ) ` R ) ) = ( ( ( X L Y ) ` R ) ( <. ( F ` X ) , ( K ` X ) >. .x. ( K ` Y ) ) ( A ` X ) ) )

  proof
    wph
    vy
    cv
    #
    cA
    cfv
    #
    vf
    cv
    #
    vx
    cv
    #
    @0
    cG
    co
    #
    cfv
    #
    @3
    cF
    cfv
    #
    @0
    cF
    cfv
    #
    cop
    #
    @0
    cK
    cfv
    #
    c.x
    co
    #
    co
    #
    @2
    @3
    @0
    cL
    co
    #
    cfv
    #
    @3
    cA
    cfv
    #
    @6
    @3
    cK
    cfv
    #
    cop
    #
    @9
    c.x
    co
    #
    co
    #
    wceq
    #
    vf
    @3
    @0
    cH
    co
    #
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    cY
    cA
    cfv
    #
    cR
    cX
    cY
    cG
    co
    #
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
    cop
    #
    cY
    cK
    cfv
    #
    c.x
    co
    #
    co
    #
    cR
    cX
    cY
    cL
    co
    #
    cfv
    #
    cX
    cA
    cfv
    #
    @27
    cX
    cK
    cfv
    #
    cop
    #
    @30
    c.x
    co
    #
    co
    #
    wceq
    #
    wph
    cA
    vx
    cB
    @6
    @15
    cD
    chom
    cfv
    #
    co
    cixp
    wcel
    #
    @23
    wph
    cA
    cF
    cG
    cop
    #
    cK
    cL
    cop
    #
    cN
    co
    wcel
    #
    @42
    @23
    wa
    natixp.2
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    c.x
    vf
    cF
    cG
    cH
    @41
    cK
    cL
    cN
    natrcl.1
    natixp.b
    nati.h
    @41
    eqid
    nati.o
    wph
    @43
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    cF
    cG
    @46
    wbr
    wph
    @47
    @44
    @46
    wcel
    #
    wph
    @45
    @47
    @48
    wa
    natixp.2
    cA
    cC
    cD
    @43
    @44
    cN
    natrcl.1
    natrcl
    syl
    #
    simpld
    cF
    cG
    @46
    df-br
    sylibr
    wph
    @48
    cK
    cL
    @46
    wbr
    wph
    @47
    @48
    @49
    simprd
    cK
    cL
    @46
    df-br
    sylibr
    isnat
    mpbid
    simprd
    wph
    @22
    @40
    vx
    cX
    cB
    nati.x
    wph
    @3
    cX
    wceq
    #
    wa
    #
    @21
    @40
    vy
    cY
    cB
    wph
    cY
    cB
    wcel
    @50
    nati.y
    adantr
    @51
    @0
    cY
    wceq
    #
    wa
    #
    @19
    @40
    vf
    cR
    @20
    @53
    cR
    cX
    cY
    cH
    co
    #
    @20
    wph
    cR
    @54
    wcel
    @50
    @52
    nati.r
    ad2antrr
    @53
    @3
    cX
    @0
    cY
    cH
    wph
    @50
    @52
    simplr
    @51
    @52
    simpr
    oveq12d
    eleqtrrd
    @53
    @2
    cR
    wceq
    #
    wa
    #
    @11
    @32
    @18
    @39
    @56
    @1
    @24
    @5
    @26
    @10
    @31
    @56
    @8
    @29
    @9
    @30
    c.x
    @56
    @6
    @27
    @7
    @28
    @56
    @3
    cX
    cF
    wph
    @50
    @52
    @55
    simpllr
    #
    fveq2d
    #
    @56
    @0
    cY
    cF
    @51
    @52
    @55
    simplr
    #
    fveq2d
    opeq12d
    @56
    @0
    cY
    cK
    @59
    fveq2d
    #
    oveq12d
    @56
    @0
    cY
    cA
    @59
    fveq2d
    @56
    @2
    cR
    @4
    @25
    @56
    @3
    cX
    @0
    cY
    cG
    @57
    @59
    oveq12d
    @53
    @55
    simpr
    #
    fveq12d
    oveq123d
    @56
    @13
    @34
    @14
    @35
    @17
    @38
    @56
    @16
    @37
    @9
    @30
    c.x
    @56
    @6
    @27
    @15
    @36
    @58
    @56
    @3
    cX
    cK
    @57
    fveq2d
    opeq12d
    @60
    oveq12d
    @56
    @2
    cR
    @12
    @33
    @56
    @3
    cX
    @0
    cY
    cL
    @57
    @59
    oveq12d
    @61
    fveq12d
    @56
    @3
    cX
    cA
    @57
    fveq2d
    oveq123d
    eqeq12d
    rspcdv
    rspcimdv
    rspcimdv
    mpd
end
