include "cop.mm"
include "ccnv.mm"
include "cvv.mm"
include "c1o.mm"
include "cdif.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "co.mm"
include "wa.mm"
include "fvex.mm"
include "dif1o.mm"
include "mpbiran.mm"
include "anbi2i.mm"
include "wfn.mm"
include "wb.mm"
include "elpreima.mm"
include "ax-mp.mm"
include "cdm.mm"
include "ndmfv.mm"
include "necon1ai.mm"
include "wceq.mm"
include "fndm.mm"
include "syl6eleq.mm"
include "pm4.71ri.mm"
include "3bitr4i.mm"
include "breqi.mm"
include "df-br.mm"
include "bitri.mm"
include "df-ov.mm"
include "neeq1i.mm"

theorem brwitnlem
  let cA: class A
  let cB: class B
  let cR: class R
  let cO: class O
  let cX: class X
  assume brwitnlem.r: |- R = ( `' O " ( _V \ 1o ) )
  assume brwitnlem.o: |- O Fn X


  assert |- ( A R B <-> ( A O B ) =/= (/) )

  proof
    cA
    cB
    cop
    #
    cO
    ccnv
    cvv
    c1o
    cdif
    #
    cima
    #
    wcel
    #
    @0
    cO
    cfv
    #
    c0
    wne
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cO
    co
    #
    c0
    wne
    @0
    cX
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @8
    @5
    wa
    @3
    @5
    @9
    @5
    @8
    @9
    @4
    cvv
    wcel
    @5
    @0
    cO
    fvex
    @4
    cvv
    dif1o
    mpbiran
    anbi2i
    cO
    cX
    wfn
    #
    @3
    @10
    wb
    brwitnlem.o
    cX
    @0
    @1
    cO
    elpreima
    ax-mp
    @5
    @8
    @5
    @0
    cO
    cdm
    #
    cX
    @0
    @12
    wcel
    @4
    c0
    @0
    cO
    ndmfv
    necon1ai
    @11
    @12
    cX
    wceq
    brwitnlem.o
    cX
    cO
    fndm
    ax-mp
    syl6eleq
    pm4.71ri
    3bitr4i
    @6
    cA
    cB
    @2
    wbr
    @3
    cA
    cB
    cR
    @2
    brwitnlem.r
    breqi
    cA
    cB
    @2
    df-br
    bitri
    @7
    @4
    c0
    cA
    cB
    cO
    df-ov
    neeq1i
    3bitr4i
end
