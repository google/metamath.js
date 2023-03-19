include "wrel.mm"
include "cid.mm"
include "cdif.mm"
include "wbr.mm"
include "wne.mm"
include "wa.mm"
include "cop.mm"
include "wcel.mm"
include "cvv.mm"
include "reldif.mm"
include "brrelex2.mm"
include "sylan.mm"
include "adantrr.mm"
include "wn.mm"
include "brdif.mm"
include "ideqg.mm"
include "necon3bbid.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "pm5.21nd.mm"
include "df-br.mm"
include "anbi1i.mm"
include "3bitr3g.mm"

theorem opeldifid
  let cA: class A
  let cX: class X
  let cY: class Y


  assert |- ( Rel A -> ( <. X , Y >. e. ( A \ _I ) <-> ( <. X , Y >. e. A /\ X =/= Y ) ) )

  proof
    cA
    wrel
    #
    cX
    cY
    cA
    cid
    cdif
    #
    wbr
    #
    cX
    cY
    cA
    wbr
    #
    cX
    cY
    wne
    #
    wa
    #
    cX
    cY
    cop
    #
    @1
    wcel
    @6
    cA
    wcel
    #
    @4
    wa
    @0
    @2
    @5
    cY
    cvv
    wcel
    #
    @0
    @1
    wrel
    @2
    @8
    cA
    cid
    reldif
    cX
    cY
    @1
    brrelex2
    sylan
    @0
    @3
    @8
    @4
    cX
    cY
    cA
    brrelex2
    adantrr
    @2
    @3
    cX
    cY
    cid
    wbr
    #
    wn
    #
    wa
    @8
    @5
    cX
    cY
    cA
    cid
    brdif
    @8
    @10
    @4
    @3
    @8
    @9
    cX
    cY
    cX
    cY
    cvv
    ideqg
    necon3bbid
    anbi2d
    syl5bb
    pm5.21nd
    cX
    cY
    @1
    df-br
    @3
    @7
    @4
    cX
    cY
    cA
    df-br
    anbi1i
    3bitr3g
end
