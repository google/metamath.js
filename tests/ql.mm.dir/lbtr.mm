include "wa.mm"
include "ax-r1.mm"
include "lan.mm"
include "df2le2.mm"
include "ax-r2.mm"
include "df2le1.mm"

theorem lbtr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume lbtr.1: |- a =< b
  assume lbtr.2: |- b = c


  assert |- a =< c

  proof
    wva
    wvc
    wva
    wvc
    wa
    wva
    wvb
    wa
    wva
    wvc
    wvb
    wva
    wvb
    wvc
    lbtr.2
    ax-r1
    lan
    wva
    wvb
    lbtr.1
    df2le2
    ax-r2
    df2le1
end
