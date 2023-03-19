include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "ccss.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "iscss.mm"
include "syl.mm"
include "ibi.mm"

theorem cssi
  let cC: class C
  let cS: class S
  let c.pe: class ._|_
  let cW: class W
  let vs: setvar s
  let vw: setvar w
  assume cssval.o: |- ._|_ = ( ocv ` W )
  assume cssval.c: |- C = ( CSubSp ` W )


  assert |- ( S e. C -> S = ( ._|_ ` ( ._|_ ` S ) ) )

  proof
    cS
    cC
    wcel
    #
    cS
    cS
    c.pe
    cfv
    c.pe
    cfv
    wceq
    #
    @0
    cW
    ccss
    cdm
    #
    wcel
    #
    @0
    @1
    wb
    @3
    cS
    cW
    ccss
    cfv
    cC
    cS
    cW
    ccss
    elfvdm
    cssval.c
    eleq2s
    cC
    cS
    c.pe
    cW
    @2
    cssval.o
    cssval.c
    iscss
    syl
    ibi
end
