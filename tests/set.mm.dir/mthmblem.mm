include "wcel.mm"
include "cmpst.mm"
include "cfv.mm"
include "cmpps.mm"
include "cima.mm"
include "wa.mm"
include "wceq.mm"
include "ccnv.mm"
include "eqid.mm"
include "mthmval.mm"
include "eleq2i.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "msrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "elpreima.mm"
include "bitri.mm"
include "eleq1.mm"
include "cv.mm"
include "wrex.mm"
include "wfun.mm"
include "ffun.mm"
include "fvelima.mm"
include "mpan.mm"
include "mthmi.mm"
include "rexlimiva.mm"
include "syl.mm"
include "syl6bi.mm"
include "adantld.mm"
include "syl5bi.mm"

theorem mthmblem
  let cR: class R
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume mthmb.r: |- R = ( mStRed ` T )
  assume mthmb.u: |- U = ( mThm ` T )


  assert |- ( ( R ` X ) = ( R ` Y ) -> ( X e. U -> Y e. U ) )

  proof
    cX
    cU
    wcel
    #
    cX
    cT
    cmpst
    cfv
    #
    wcel
    #
    cX
    cR
    cfv
    #
    cR
    cT
    cmpps
    cfv
    #
    cima
    #
    wcel
    #
    wa
    #
    @3
    cY
    cR
    cfv
    #
    wceq
    #
    cY
    cU
    wcel
    #
    @0
    cX
    cR
    ccnv
    @5
    cima
    #
    wcel
    #
    @7
    cU
    @11
    cX
    cR
    cT
    cU
    @4
    mthmb.r
    @4
    eqid
    #
    mthmb.u
    mthmval
    eleq2i
    cR
    @1
    wfn
    #
    @12
    @7
    wb
    @1
    @1
    cR
    wf
    #
    @14
    @1
    cR
    cT
    @1
    eqid
    mthmb.r
    msrf
    #
    @1
    @1
    cR
    ffn
    ax-mp
    @1
    cX
    @5
    cR
    elpreima
    ax-mp
    bitri
    @9
    @6
    @10
    @2
    @9
    @6
    @8
    @5
    wcel
    #
    @10
    @3
    @8
    @5
    eleq1
    @17
    vx
    cv
    #
    cR
    cfv
    @8
    wceq
    #
    vx
    @4
    wrex
    #
    @10
    cR
    wfun
    #
    @17
    @20
    @15
    @21
    @16
    @1
    @1
    cR
    ffun
    ax-mp
    vx
    @8
    @4
    cR
    fvelima
    mpan
    @19
    @10
    vx
    @4
    cR
    cT
    cU
    @4
    @18
    cY
    mthmb.r
    @13
    mthmb.u
    mthmi
    rexlimiva
    syl
    syl6bi
    adantld
    syl5bi
end
