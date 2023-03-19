include "wcel.mm"
include "cvv.mm"
include "a1i.mm"
include "ccnv.mm"
include "wfun.mm"
include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "id.mm"
include "strfv2d.mm"

theorem strfv2
  let cC: class C
  let cS: class S
  let cE: class E
  let cV: class V
  assume strfv2.s: |- S e. _V
  assume strfv2.f: |- Fun `' `' S
  assume strfv2.e: |- E = Slot ( E ` ndx )
  assume strfv2.n: |- <. ( E ` ndx ) , C >. e. S


  assert |- ( C e. V -> C = ( E ` S ) )

  proof
    cC
    cV
    wcel
    #
    cC
    cS
    cE
    cvv
    cV
    strfv2.e
    cS
    cvv
    wcel
    @0
    strfv2.s
    a1i
    cS
    ccnv
    ccnv
    wfun
    @0
    strfv2.f
    a1i
    cnx
    cE
    cfv
    cC
    cop
    cS
    wcel
    @0
    strfv2.n
    a1i
    @0
    id
    strfv2d
end
