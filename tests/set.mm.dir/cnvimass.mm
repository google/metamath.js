include "ccnv.mm"
include "cima.mm"
include "crn.mm"
include "cdm.mm"
include "imassrn.mm"
include "dfdm4.mm"
include "sseqtr4i.mm"

theorem cnvimass
  let cA: class A
  let cB: class B


  assert |- ( `' A " B ) C_ dom A

  proof
    cA
    ccnv
    #
    cB
    cima
    @0
    crn
    cA
    cdm
    @0
    cB
    imassrn
    cA
    dfdm4
    sseqtr4i
end
