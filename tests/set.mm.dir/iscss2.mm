include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "iscss.mm"
include "adantr.mm"
include "ocvocv.mm"
include "eqss.mm"
include "baib.mm"
include "syl.mm"
include "bitrd.mm"

theorem iscss2
  let cC: class C
  let cS: class S
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume cssss.v: |- V = ( Base ` W )
  assume cssss.c: |- C = ( CSubSp ` W )
  assume ocvcss.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( W e. PreHil /\ S C_ V ) -> ( S e. C <-> ( ._|_ ` ( ._|_ ` S ) ) C_ S ) )

  proof
    cW
    cphl
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
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
    #
    wceq
    #
    @4
    cS
    wss
    #
    @0
    @3
    @5
    wb
    @1
    cC
    cS
    c.pe
    cW
    cphl
    ocvcss.o
    cssss.c
    iscss
    adantr
    @2
    cS
    @4
    wss
    #
    @5
    @6
    wb
    cS
    c.pe
    cV
    cW
    cssss.v
    ocvcss.o
    ocvocv
    @5
    @7
    @6
    cS
    @4
    eqss
    baib
    syl
    bitrd
end
