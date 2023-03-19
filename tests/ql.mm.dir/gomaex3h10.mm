include "wo.mm"
include "wn.mm"
include "wa.mm"
include "lea.mm"
include "wi1.mm"
include "df-i1.mm"
include "ax-r4.mm"
include "anor1.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "ax-a1.mm"
include "le3tr1.mm"

theorem gomaex3h10
  let wvb: term b
  let wvc: term c
  let wve: term e
  let wvf: term f
  let wvq: term q
  let wvx: term x
  let wvy: term y
  assume gomaex3h10.10: |- q = ( ( e v f ) ->1 ( b v c ) ' ) '
  assume gomaex3h10.21: |- x = q
  assume gomaex3h10.22: |- y = ( e v f ) '


  assert |- x =< y '

  proof
    wvq
    wve
    wvf
    wo
    #
    wn
    #
    wn
    #
    wvx
    wvy
    wn
    @0
    @0
    wvb
    wvc
    wo
    wn
    #
    wa
    #
    wn
    #
    wa
    #
    @0
    wvq
    @2
    @0
    @5
    lea
    wvq
    @0
    @3
    wi1
    #
    wn
    #
    @6
    gomaex3h10.10
    @8
    @1
    @4
    wo
    #
    wn
    #
    @6
    @7
    @9
    @0
    @3
    df-i1
    ax-r4
    @6
    @10
    @0
    @4
    anor1
    ax-r1
    ax-r2
    ax-r2
    @0
    @2
    @0
    ax-a1
    ax-r1
    le3tr1
    gomaex3h10.21
    wvy
    @1
    gomaex3h10.22
    ax-r4
    le3tr1
end
