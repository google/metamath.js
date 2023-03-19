include "wcel.mm"
include "clinds.mm"
include "cfv.mm"
include "cbs.mm"
include "cpw.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "fveq2.mm"
include "pweqd.mm"
include "breq2.mm"
include "rabeqbidv.mm"
include "df-linds.mm"
include "fvex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"
include "reseq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "elpw2.mm"
include "sseq2i.mm"
include "bitr4i.mm"
include "anbi1i.mm"

theorem islinds
  let cB: class B
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  assume islinds.b: |- B = ( Base ` W )


  assert |- ( W e. V -> ( X e. ( LIndS ` W ) <-> ( X C_ B /\ ( _I |` X ) LIndF W ) ) )

  proof
    cW
    cV
    wcel
    #
    cX
    cW
    clinds
    cfv
    #
    wcel
    #
    cX
    cW
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    cid
    cX
    cres
    #
    cW
    clindf
    wbr
    #
    wa
    #
    cX
    cB
    wss
    #
    @7
    wa
    @0
    @2
    cX
    cid
    vs
    cv
    #
    cres
    #
    cW
    clindf
    wbr
    #
    vs
    @4
    crab
    #
    wcel
    @8
    @0
    @1
    @13
    cX
    @0
    cW
    cvv
    wcel
    @1
    @13
    wceq
    cW
    cV
    elex
    vw
    cW
    @11
    vw
    cv
    #
    clindf
    wbr
    #
    vs
    @14
    cbs
    cfv
    #
    cpw
    #
    crab
    @13
    cvv
    clinds
    @14
    cW
    wceq
    #
    @15
    @12
    vs
    @17
    @4
    @18
    @16
    @3
    @14
    cW
    cbs
    fveq2
    pweqd
    @14
    cW
    @11
    clindf
    breq2
    rabeqbidv
    vw
    vs
    df-linds
    @12
    vs
    @4
    @3
    cW
    cbs
    fvex
    #
    pwex
    rabex
    fvmpt
    syl
    eleq2d
    @12
    @7
    vs
    cX
    @4
    @10
    cX
    wceq
    @11
    @6
    cW
    clindf
    @10
    cX
    cid
    reseq2
    breq1d
    elrab
    syl6bb
    @5
    @9
    @7
    @5
    cX
    @3
    wss
    @9
    cX
    @3
    @19
    elpw2
    cB
    @3
    cX
    islinds.b
    sseq2i
    bitr4i
    anbi1i
    syl6bb
end
