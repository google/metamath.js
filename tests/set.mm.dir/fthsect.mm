include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "co.mm"
include "ccid.mm"
include "wceq.mm"
include "wbr.mm"
include "chom.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "cfunc.mm"
include "wa.mm"
include "cfth.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "simpld.mm"
include "catcocl.mm"
include "catidcl.mm"
include "fthi.mm"
include "funcco.mm"
include "funcid.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "issect2.mm"
include "cbs.mm"
include "simprd.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "funcf2.mm"
include "3bitr4d.mm"

theorem fthsect
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume fthsect.b: |- B = ( Base ` C )
  assume fthsect.h: |- H = ( Hom ` C )
  assume fthsect.f: |- ( ph -> F ( C Faith D ) G )
  assume fthsect.x: |- ( ph -> X e. B )
  assume fthsect.y: |- ( ph -> Y e. B )
  assume fthsect.m: |- ( ph -> M e. ( X H Y ) )
  assume fthsect.n: |- ( ph -> N e. ( Y H X ) )
  assume fthsect.s: |- S = ( Sect ` C )
  assume fthsect.t: |- T = ( Sect ` D )


  assert |- ( ph -> ( M ( X S Y ) N <-> ( ( X G Y ) ` M ) ( ( F ` X ) T ( F ` Y ) ) ( ( Y G X ) ` N ) ) )

  proof
    wph
    cN
    cM
    cX
    cY
    cop
    cX
    cC
    cco
    cfv
    #
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
    cN
    cY
    cX
    cG
    co
    #
    cfv
    #
    cM
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
    @9
    cD
    cco
    cfv
    #
    co
    co
    #
    @9
    cD
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    cM
    cN
    cX
    cY
    cS
    co
    wbr
    @8
    @6
    @9
    @10
    cT
    co
    wbr
    wph
    @1
    cX
    cX
    cG
    co
    #
    cfv
    #
    @3
    @16
    cfv
    #
    wceq
    @4
    @15
    wph
    cB
    cC
    cD
    @1
    @3
    cF
    cG
    cH
    cD
    chom
    cfv
    #
    cX
    cX
    fthsect.b
    fthsect.h
    @19
    eqid
    #
    fthsect.f
    fthsect.x
    fthsect.x
    wph
    cB
    cC
    @0
    cM
    cN
    cH
    cX
    cY
    cX
    fthsect.b
    fthsect.h
    @0
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
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
    @22
    @23
    wa
    wph
    cF
    cG
    @25
    wbr
    #
    @26
    wph
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    @27
    fthsect.f
    @28
    @25
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
    @25
    df-br
    sylib
    cC
    cD
    @24
    funcrcl
    syl
    #
    simpld
    #
    fthsect.x
    fthsect.y
    fthsect.x
    fthsect.m
    fthsect.n
    catcocl
    wph
    cB
    cC
    @2
    cH
    cX
    fthsect.b
    fthsect.h
    @2
    eqid
    #
    @31
    fthsect.x
    catidcl
    fthi
    wph
    @17
    @12
    @18
    @14
    wph
    cB
    cC
    @0
    cD
    cF
    cG
    cH
    cM
    cN
    @11
    cX
    cY
    cX
    fthsect.b
    fthsect.h
    @21
    @11
    eqid
    #
    @29
    fthsect.x
    fthsect.y
    fthsect.x
    fthsect.m
    fthsect.n
    funcco
    wph
    cB
    cC
    @2
    cD
    cF
    cG
    @13
    cX
    fthsect.b
    @32
    @13
    eqid
    #
    @29
    fthsect.x
    funcid
    eqeq12d
    bitr3d
    wph
    cB
    cC
    cS
    @0
    @2
    cM
    cN
    cH
    cX
    cY
    fthsect.b
    fthsect.h
    @21
    @32
    fthsect.s
    @31
    fthsect.x
    fthsect.y
    fthsect.m
    fthsect.n
    issect2
    wph
    cD
    cbs
    cfv
    #
    cD
    cT
    @11
    @13
    @8
    @6
    @19
    @9
    @10
    @35
    eqid
    #
    @20
    @33
    @34
    fthsect.t
    wph
    @22
    @23
    @30
    simprd
    wph
    cB
    @35
    cX
    cF
    wph
    cB
    @35
    cC
    cD
    cF
    cG
    fthsect.b
    @36
    @29
    funcf1
    #
    fthsect.x
    ffvelrnd
    wph
    cB
    @35
    cY
    cF
    @37
    fthsect.y
    ffvelrnd
    wph
    cX
    cY
    cH
    co
    @9
    @10
    @19
    co
    cM
    @7
    wph
    cB
    cC
    cD
    cF
    cG
    cH
    @19
    cX
    cY
    fthsect.b
    fthsect.h
    @20
    @29
    fthsect.x
    fthsect.y
    funcf2
    fthsect.m
    ffvelrnd
    wph
    cY
    cX
    cH
    co
    @10
    @9
    @19
    co
    cN
    @5
    wph
    cB
    cC
    cD
    cF
    cG
    cH
    @19
    cY
    cX
    fthsect.b
    fthsect.h
    @20
    @29
    fthsect.y
    fthsect.x
    funcf2
    fthsect.n
    ffvelrnd
    issect2
    3bitr4d
end
