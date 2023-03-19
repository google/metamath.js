include "co.mm"
include "cfv.mm"
include "wbr.mm"
include "csect.mm"
include "eqid.mm"
include "wa.mm"
include "ccat.mm"
include "wcel.mm"
include "cop.mm"
include "cfunc.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "isinv.mm"
include "mpbid.mm"
include "funcsect.mm"
include "simprd.mm"
include "cbs.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "mpbir2and.mm"

theorem funcinv
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume funcinv.b: |- B = ( Base ` D )
  assume funcinv.s: |- I = ( Inv ` D )
  assume funcinv.t: |- J = ( Inv ` E )
  assume funcinv.f: |- ( ph -> F ( D Func E ) G )
  assume funcinv.x: |- ( ph -> X e. B )
  assume funcinv.y: |- ( ph -> Y e. B )
  assume funcinv.m: |- ( ph -> M ( X I Y ) N )


  assert |- ( ph -> ( ( X G Y ) ` M ) ( ( F ` X ) J ( F ` Y ) ) ( ( Y G X ) ` N ) )

  proof
    wph
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
    cJ
    co
    wbr
    @0
    @1
    @2
    @3
    cE
    csect
    cfv
    #
    co
    wbr
    @1
    @0
    @3
    @2
    @4
    co
    wbr
    wph
    cB
    cD
    cD
    csect
    cfv
    #
    @4
    cE
    cF
    cG
    cM
    cN
    cX
    cY
    funcinv.b
    @5
    eqid
    #
    @4
    eqid
    #
    funcinv.f
    funcinv.x
    funcinv.y
    wph
    cM
    cN
    cX
    cY
    @5
    co
    wbr
    #
    cN
    cM
    cY
    cX
    @5
    co
    wbr
    #
    wph
    cM
    cN
    cX
    cY
    cI
    co
    wbr
    @8
    @9
    wa
    funcinv.m
    wph
    cB
    cD
    @5
    cM
    cN
    cI
    cX
    cY
    funcinv.b
    funcinv.s
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
    @10
    @11
    wa
    wph
    cF
    cG
    @13
    wbr
    @14
    funcinv.f
    cF
    cG
    @13
    df-br
    sylib
    cD
    cE
    @12
    funcrcl
    syl
    #
    simpld
    funcinv.x
    funcinv.y
    @6
    isinv
    mpbid
    #
    simpld
    funcsect
    wph
    cB
    cD
    @5
    @4
    cE
    cF
    cG
    cN
    cM
    cY
    cX
    funcinv.b
    @6
    @7
    funcinv.f
    funcinv.y
    funcinv.x
    wph
    @8
    @9
    @16
    simprd
    funcsect
    wph
    cE
    cbs
    cfv
    #
    cE
    @4
    @0
    @1
    cJ
    @2
    @3
    @17
    eqid
    #
    funcinv.t
    wph
    @10
    @11
    @15
    simprd
    wph
    cB
    @17
    cX
    cF
    wph
    cB
    @17
    cD
    cE
    cF
    cG
    funcinv.b
    @18
    funcinv.f
    funcf1
    #
    funcinv.x
    ffvelrnd
    wph
    cB
    @17
    cY
    cF
    @19
    funcinv.y
    ffvelrnd
    @7
    isinv
    mpbir2and
end
