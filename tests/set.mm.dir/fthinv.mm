include "csect.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "eqid.mm"
include "fthsect.mm"
include "anbi12d.mm"
include "ccat.mm"
include "wcel.mm"
include "cop.mm"
include "cfunc.mm"
include "cfth.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "simpld.mm"
include "isinv.mm"
include "cbs.mm"
include "simprd.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "3bitr4d.mm"

theorem fthinv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
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
  assume fthinv.s: |- I = ( Inv ` C )
  assume fthinv.t: |- J = ( Inv ` D )


  assert |- ( ph -> ( M ( X I Y ) N <-> ( ( X G Y ) ` M ) ( ( F ` X ) J ( F ` Y ) ) ( ( Y G X ) ` N ) ) )

  proof
    wph
    cM
    cN
    cX
    cY
    cC
    csect
    cfv
    #
    co
    wbr
    #
    cN
    cM
    cY
    cX
    @0
    co
    wbr
    #
    wa
    cM
    cX
    cY
    cG
    co
    cfv
    #
    cN
    cY
    cX
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
    cD
    csect
    cfv
    #
    co
    wbr
    #
    @4
    @3
    @6
    @5
    @7
    co
    wbr
    #
    wa
    cM
    cN
    cX
    cY
    cI
    co
    wbr
    @3
    @4
    @5
    @6
    cJ
    co
    wbr
    wph
    @1
    @8
    @2
    @9
    wph
    cB
    cC
    cD
    @0
    @7
    cF
    cG
    cH
    cM
    cN
    cX
    cY
    fthsect.b
    fthsect.h
    fthsect.f
    fthsect.x
    fthsect.y
    fthsect.m
    fthsect.n
    @0
    eqid
    #
    @7
    eqid
    #
    fthsect
    wph
    cB
    cC
    cD
    @0
    @7
    cF
    cG
    cH
    cN
    cM
    cY
    cX
    fthsect.b
    fthsect.h
    fthsect.f
    fthsect.y
    fthsect.x
    fthsect.n
    fthsect.m
    @10
    @11
    fthsect
    anbi12d
    wph
    cB
    cC
    @0
    cM
    cN
    cI
    cX
    cY
    fthsect.b
    fthinv.s
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
    @12
    @13
    wa
    wph
    cF
    cG
    @15
    wbr
    #
    @16
    wph
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    @17
    fthsect.f
    @18
    @15
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
    @15
    df-br
    sylib
    cC
    cD
    @14
    funcrcl
    syl
    #
    simpld
    fthsect.x
    fthsect.y
    @10
    isinv
    wph
    cD
    cbs
    cfv
    #
    cD
    @7
    @3
    @4
    cJ
    @5
    @6
    @21
    eqid
    #
    fthinv.t
    wph
    @12
    @13
    @20
    simprd
    wph
    cB
    @21
    cX
    cF
    wph
    cB
    @21
    cC
    cD
    cF
    cG
    fthsect.b
    @22
    @19
    funcf1
    #
    fthsect.x
    ffvelrnd
    wph
    cB
    @21
    cY
    cF
    @23
    fthsect.y
    ffvelrnd
    @11
    isinv
    3bitr4d
end
