include "wn.mm"
include "wo.mm"
include "wa.mm"
include "lea.mm"
include "lear.mm"
include "leo.mm"
include "lel2or.mm"
include "letr.mm"
include "ler2an.mm"
include "leor.mm"
include "lebi.mm"

theorem womao
  let wva: term a
  let wvb: term b


  assert |- ( a ' ^ ( a v ( a ' ^ ( a v b ) ) ) ) = ( a ' ^ ( a v b ) )

  proof
    wva
    wn
    #
    wva
    @0
    wva
    wvb
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    @2
    @4
    @0
    @1
    @0
    @3
    lea
    @4
    @3
    @1
    @0
    @3
    lear
    wva
    @1
    @2
    wva
    wvb
    leo
    @0
    @1
    lear
    lel2or
    letr
    ler2an
    @2
    @0
    @3
    @0
    @1
    lea
    @2
    wva
    leor
    ler2an
    lebi
end
