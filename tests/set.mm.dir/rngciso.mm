include "co.mm"
include "wcel.mm"
include "cinv.mm"
include "cfv.mm"
include "cdm.mm"
include "crngs.mm"
include "eqid.mm"
include "ccat.mm"
include "rngccat.mm"
include "syl.mm"
include "isoval.mm"
include "eleq2d.mm"
include "wbr.mm"
include "wfun.mm"
include "wb.mm"
include "invfun.mm"
include "funfvbrb.mm"
include "ccnv.mm"
include "wceq.mm"
include "wa.mm"
include "rngcinv.mm"
include "simpl.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "wrel.mm"
include "wi.mm"
include "funrel.mm"
include "releldm.mm"
include "ex.mm"
include "sylbird.mm"
include "mpan2i.mm"
include "impbid.mm"
include "bitrd.mm"

theorem rngciso
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume rngcsect.c: |- C = ( RngCat ` U )
  assume rngcsect.b: |- B = ( Base ` C )
  assume rngcsect.u: |- ( ph -> U e. V )
  assume rngcsect.x: |- ( ph -> X e. B )
  assume rngcsect.y: |- ( ph -> Y e. B )
  assume rngciso.n: |- I = ( Iso ` C )


  assert |- ( ph -> ( F e. ( X I Y ) <-> F e. ( X RngIsom Y ) ) )

  proof
    wph
    cF
    cX
    cY
    cI
    co
    #
    wcel
    cF
    cX
    cY
    cC
    cinv
    cfv
    #
    co
    #
    cdm
    #
    wcel
    #
    cF
    cX
    cY
    crngs
    co
    wcel
    #
    wph
    @0
    @3
    cF
    wph
    cB
    cC
    cI
    @1
    cX
    cY
    rngcsect.b
    @1
    eqid
    #
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    rngcsect.u
    cC
    cU
    cV
    rngcsect.c
    rngccat
    syl
    #
    rngcsect.x
    rngcsect.y
    rngciso.n
    isoval
    eleq2d
    wph
    @4
    @5
    wph
    @4
    cF
    cF
    @2
    cfv
    #
    @2
    wbr
    #
    @5
    wph
    @2
    wfun
    #
    @4
    @9
    wb
    wph
    cB
    cC
    @1
    cX
    cY
    rngcsect.b
    @6
    @7
    rngcsect.x
    rngcsect.y
    invfun
    #
    cF
    @2
    funfvbrb
    syl
    wph
    @9
    @5
    @8
    cF
    ccnv
    #
    wceq
    #
    wa
    @5
    wph
    cB
    cC
    cU
    cF
    @8
    @1
    cV
    cX
    cY
    rngcsect.c
    rngcsect.b
    rngcsect.u
    rngcsect.x
    rngcsect.y
    @6
    rngcinv
    @5
    @13
    simpl
    syl6bi
    sylbid
    wph
    @5
    @12
    @12
    wceq
    #
    @4
    @12
    eqid
    wph
    @5
    @14
    wa
    cF
    @12
    @2
    wbr
    #
    @4
    wph
    cB
    cC
    cU
    cF
    @12
    @1
    cV
    cX
    cY
    rngcsect.c
    rngcsect.b
    rngcsect.u
    rngcsect.x
    rngcsect.y
    @6
    rngcinv
    wph
    @2
    wrel
    #
    @15
    @4
    wi
    wph
    @10
    @16
    @11
    @2
    funrel
    syl
    @16
    @15
    @4
    cF
    @12
    @2
    releldm
    ex
    syl
    sylbird
    mpan2i
    impbid
    bitrd
end
