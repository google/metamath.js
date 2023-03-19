include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "cinv.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "cop.mm"
include "cfunc.mm"
include "wa.mm"
include "wbr.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simprd.mm"
include "funcf1.mm"
include "ffvelrnd.mm"
include "cdm.mm"
include "simpld.mm"
include "isoval.mm"
include "eleqtrd.mm"
include "wfun.mm"
include "wb.mm"
include "invfun.mm"
include "funfvbrb.mm"
include "mpbid.mm"
include "funcinv.mm"
include "inviso1.mm"

theorem funciso
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cM: class M
  let cX: class X
  let cY: class Y
  assume funciso.b: |- B = ( Base ` D )
  assume funciso.s: |- I = ( Iso ` D )
  assume funciso.t: |- J = ( Iso ` E )
  assume funciso.f: |- ( ph -> F ( D Func E ) G )
  assume funciso.x: |- ( ph -> X e. B )
  assume funciso.y: |- ( ph -> Y e. B )
  assume funciso.m: |- ( ph -> M e. ( X I Y ) )


  assert |- ( ph -> ( ( X G Y ) ` M ) e. ( ( F ` X ) J ( F ` Y ) ) )

  proof
    wph
    cE
    cbs
    cfv
    #
    cE
    cM
    cX
    cY
    cG
    co
    cfv
    cM
    cX
    cY
    cD
    cinv
    cfv
    #
    co
    #
    cfv
    #
    cY
    cX
    cG
    co
    cfv
    cJ
    cE
    cinv
    cfv
    #
    cX
    cF
    cfv
    cY
    cF
    cfv
    @0
    eqid
    #
    @4
    eqid
    #
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
    @7
    @8
    wa
    wph
    cF
    cG
    @10
    wbr
    @11
    funciso.f
    cF
    cG
    @10
    df-br
    sylib
    cD
    cE
    @9
    funcrcl
    syl
    #
    simprd
    wph
    cB
    @0
    cX
    cF
    wph
    cB
    @0
    cD
    cE
    cF
    cG
    funciso.b
    @5
    funciso.f
    funcf1
    #
    funciso.x
    ffvelrnd
    wph
    cB
    @0
    cY
    cF
    @13
    funciso.y
    ffvelrnd
    funciso.t
    wph
    cB
    cD
    cE
    cF
    cG
    @1
    @4
    cM
    @3
    cX
    cY
    funciso.b
    @1
    eqid
    #
    @6
    funciso.f
    funciso.x
    funciso.y
    wph
    cM
    @2
    cdm
    #
    wcel
    #
    cM
    @3
    @2
    wbr
    #
    wph
    cM
    cX
    cY
    cI
    co
    @15
    funciso.m
    wph
    cB
    cD
    cI
    @1
    cX
    cY
    funciso.b
    @14
    wph
    @7
    @8
    @12
    simpld
    #
    funciso.x
    funciso.y
    funciso.s
    isoval
    eleqtrd
    wph
    @2
    wfun
    @16
    @17
    wb
    wph
    cB
    cD
    @1
    cX
    cY
    funciso.b
    @14
    @18
    funciso.x
    funciso.y
    invfun
    cM
    @2
    funfvbrb
    syl
    mpbid
    funcinv
    inviso1
end
