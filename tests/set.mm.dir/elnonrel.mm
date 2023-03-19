include "cop.mm"
include "ccnv.mm"
include "cdif.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "wa.mm"
include "wn.mm"
include "nonrel.mm"
include "eleq2i.mm"
include "eldif.mm"
include "opelxp.mm"
include "notbii.mm"
include "anbi2i.mm"
include "opprc.mm"
include "eleq1d.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem elnonrel
  let cA: class A
  let cX: class X
  let cY: class Y


  assert |- ( <. X , Y >. e. ( A \ `' `' A ) <-> ( (/) e. A /\ -. ( X e. _V /\ Y e. _V ) ) )

  proof
    cX
    cY
    cop
    #
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    wcel
    @0
    cA
    cvv
    cvv
    cxp
    #
    cdif
    #
    wcel
    #
    c0
    cA
    wcel
    #
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    wa
    #
    wn
    #
    wa
    #
    @1
    @3
    @0
    cA
    nonrel
    eleq2i
    @4
    @0
    cA
    wcel
    #
    @0
    @2
    wcel
    #
    wn
    #
    wa
    #
    @8
    @0
    cA
    @2
    eldif
    @12
    @9
    @7
    wa
    @8
    @11
    @7
    @9
    @10
    @6
    cX
    cY
    cvv
    cvv
    opelxp
    notbii
    anbi2i
    @7
    @9
    @5
    @7
    @0
    c0
    cA
    cX
    cY
    opprc
    eleq1d
    pm5.32ri
    bitri
    bitri
    bitri
end
