include "co.mm"
include "cfv.mm"
include "wbr.mm"
include "cop.mm"
include "cco.mm"
include "ccid.mm"
include "wceq.mm"
include "chom.mm"
include "wcel.mm"
include "w3a.mm"
include "eqid.mm"
include "ccat.mm"
include "cfunc.mm"
include "wa.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "issect.mm"
include "mpbid.mm"
include "simp3d.mm"
include "fveq2d.mm"
include "simp1d.mm"
include "simp2d.mm"
include "funcco.mm"
include "funcid.mm"
include "3eqtr3d.mm"
include "cbs.mm"
include "simprd.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "funcf2.mm"
include "issect2.mm"
include "mpbird.mm"

theorem funcsect
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume funcsect.b: |- B = ( Base ` D )
  assume funcsect.s: |- S = ( Sect ` D )
  assume funcsect.t: |- T = ( Sect ` E )
  assume funcsect.f: |- ( ph -> F ( D Func E ) G )
  assume funcsect.x: |- ( ph -> X e. B )
  assume funcsect.y: |- ( ph -> Y e. B )
  assume funcsect.m: |- ( ph -> M ( X S Y ) N )


  assert |- ( ph -> ( ( X G Y ) ` M ) ( ( F ` X ) T ( F ` Y ) ) ( ( Y G X ) ` N ) )

  proof
    wph
    cM
    cX
    cY
    cG
    co
    #
    cfv
    #
    cN
    cY
    cX
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
    cT
    co
    wbr
    @3
    @1
    @4
    @5
    cop
    @4
    cE
    cco
    cfv
    #
    co
    co
    #
    @4
    cE
    ccid
    cfv
    #
    cfv
    #
    wceq
    wph
    cN
    cM
    cX
    cY
    cop
    cX
    cD
    cco
    cfv
    #
    co
    co
    #
    cX
    cX
    cG
    co
    #
    cfv
    cX
    cD
    ccid
    cfv
    #
    cfv
    #
    @12
    cfv
    @7
    @9
    wph
    @11
    @14
    @12
    wph
    cM
    cX
    cY
    cD
    chom
    cfv
    #
    co
    #
    wcel
    #
    cN
    cY
    cX
    @15
    co
    #
    wcel
    #
    @11
    @14
    wceq
    #
    wph
    cM
    cN
    cX
    cY
    cS
    co
    wbr
    @17
    @19
    @20
    w3a
    funcsect.m
    wph
    cB
    cD
    cS
    @10
    @13
    cM
    cN
    @15
    cX
    cY
    funcsect.b
    @15
    eqid
    #
    @10
    eqid
    #
    @13
    eqid
    #
    funcsect.s
    wph
    cD
    ccat
    wcel
    #
    cE
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    cD
    cE
    cfunc
    co
    #
    wcel
    #
    @24
    @25
    wa
    wph
    cF
    cG
    @27
    wbr
    @28
    funcsect.f
    cF
    cG
    @27
    df-br
    sylib
    cD
    cE
    @26
    funcrcl
    syl
    #
    simpld
    funcsect.x
    funcsect.y
    issect
    mpbid
    #
    simp3d
    fveq2d
    wph
    cB
    cD
    @10
    cE
    cF
    cG
    @15
    cM
    cN
    @6
    cX
    cY
    cX
    funcsect.b
    @21
    @22
    @6
    eqid
    #
    funcsect.f
    funcsect.x
    funcsect.y
    funcsect.x
    wph
    @17
    @19
    @20
    @30
    simp1d
    #
    wph
    @17
    @19
    @20
    @30
    simp2d
    #
    funcco
    wph
    cB
    cD
    @13
    cE
    cF
    cG
    @8
    cX
    funcsect.b
    @23
    @8
    eqid
    #
    funcsect.f
    funcsect.x
    funcid
    3eqtr3d
    wph
    cE
    cbs
    cfv
    #
    cE
    cT
    @6
    @8
    @1
    @3
    cE
    chom
    cfv
    #
    @4
    @5
    @35
    eqid
    #
    @36
    eqid
    #
    @31
    @34
    funcsect.t
    wph
    @24
    @25
    @29
    simprd
    wph
    cB
    @35
    cX
    cF
    wph
    cB
    @35
    cD
    cE
    cF
    cG
    funcsect.b
    @37
    funcsect.f
    funcf1
    #
    funcsect.x
    ffvelrnd
    wph
    cB
    @35
    cY
    cF
    @39
    funcsect.y
    ffvelrnd
    wph
    @16
    @4
    @5
    @36
    co
    cM
    @0
    wph
    cB
    cD
    cE
    cF
    cG
    @15
    @36
    cX
    cY
    funcsect.b
    @21
    @38
    funcsect.f
    funcsect.x
    funcsect.y
    funcf2
    @32
    ffvelrnd
    wph
    @18
    @5
    @4
    @36
    co
    cN
    @2
    wph
    cB
    cD
    cE
    cF
    cG
    @15
    @36
    cY
    cX
    funcsect.b
    @21
    @38
    funcsect.f
    funcsect.y
    funcsect.x
    funcf2
    @33
    ffvelrnd
    issect2
    mpbird
end
