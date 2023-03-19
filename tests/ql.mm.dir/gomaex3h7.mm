include "wn.mm"
include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "leor.mm"
include "df-i1.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "lecon.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h7
  let wvn: term n
  let wvp: term p
  let wvq: term q
  let wvu: term u
  assume gomaex3h7.18: |- n = ( p ' ->1 q ) '
  assume gomaex3h7.19: |- u = ( p ' ^ q )


  assert |- n =< u '

  proof
    wvp
    wn
    #
    wvq
    wi1
    #
    wn
    @0
    wvq
    wa
    #
    wn
    wvn
    wvu
    wn
    @2
    @1
    @2
    @0
    wn
    #
    @2
    wo
    #
    @1
    @2
    @3
    leor
    @1
    @4
    @0
    wvq
    df-i1
    ax-r1
    lbtr
    lecon
    gomaex3h7.18
    wvu
    @2
    gomaex3h7.19
    ax-r4
    le3tr1
end
