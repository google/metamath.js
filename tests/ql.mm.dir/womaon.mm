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

theorem womaon
  let wva: term a
  let wvb: term b


  assert |- ( a ^ ( a ' v ( a ^ ( a ' v b ) ) ) ) = ( a ^ ( a ' v b ) )

  proof
    wva
    wva
    wn
    #
    wva
    @0
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
    wva
    @1
    wva
    @3
    lea
    @4
    @3
    @1
    wva
    @3
    lear
    @0
    @1
    @2
    @0
    wvb
    leo
    wva
    @1
    lear
    lel2or
    letr
    ler2an
    @2
    wva
    @3
    wva
    @1
    lea
    @2
    @0
    leor
    ler2an
    lebi
end
