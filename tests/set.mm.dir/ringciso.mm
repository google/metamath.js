include "co.mm"
include "wcel.mm"
include "cinv.mm"
include "cfv.mm"
include "cdm.mm"
include "crs.mm"
include "eqid.mm"
include "ccat.mm"
include "ringccat.mm"
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
include "ringcinv.mm"
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

theorem ringciso
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
  assume ringcsect.c: |- C = ( RingCat ` U )
  assume ringcsect.b: |- B = ( Base ` C )
  assume ringcsect.u: |- ( ph -> U e. V )
  assume ringcsect.x: |- ( ph -> X e. B )
  assume ringcsect.y: |- ( ph -> Y e. B )
  assume ringciso.n: |- I = ( Iso ` C )


  assert |- ( ph -> ( F e. ( X I Y ) <-> F e. ( X RingIso Y ) ) )

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
    crs
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
    ringcsect.b
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
    ringcsect.u
    cC
    cU
    cV
    ringcsect.c
    ringccat
    syl
    #
    ringcsect.x
    ringcsect.y
    ringciso.n
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
    ringcsect.b
    @6
    @7
    ringcsect.x
    ringcsect.y
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
    ringcsect.c
    ringcsect.b
    ringcsect.u
    ringcsect.x
    ringcsect.y
    @6
    ringcinv
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
    ringcsect.c
    ringcsect.b
    ringcsect.u
    ringcsect.x
    ringcsect.y
    @6
    ringcinv
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
