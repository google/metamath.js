include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cdif.mm"
include "wbr.mm"
include "c0.mm"
include "br0.mm"
include "cnvnonrel.mm"
include "breqi.mm"
include "wb.mm"
include "brcnvg.mm"
include "ancoms.mm"
include "syl5rbbr.mm"
include "mtbiri.mm"

theorem brnonrel
  let cA: class A
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. U /\ Y e. V ) -> -. X ( A \ `' `' A ) Y )

  proof
    cX
    cU
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cY
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    wbr
    #
    cY
    cX
    c0
    wbr
    #
    cY
    cX
    br0
    @5
    cY
    cX
    @3
    ccnv
    #
    wbr
    #
    @2
    @4
    cY
    cX
    @6
    c0
    cA
    cnvnonrel
    breqi
    @1
    @0
    @7
    @4
    wb
    cY
    cX
    cV
    cU
    @3
    brcnvg
    ancoms
    syl5rbbr
    mtbiri
end
