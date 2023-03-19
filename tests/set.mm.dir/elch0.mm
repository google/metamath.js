include "c0h.mm"
include "wcel.mm"
include "c0v.mm"
include "csn.mm"
include "wceq.mm"
include "df-ch0.mm"
include "eleq2i.mm"
include "chil.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "elsn2.mm"
include "bitri.mm"

theorem elch0
  let cA: class A


  assert |- ( A e. 0H <-> A = 0h )

  proof
    cA
    c0h
    wcel
    cA
    c0v
    csn
    #
    wcel
    cA
    c0v
    wceq
    c0h
    @0
    cA
    df-ch0
    eleq2i
    cA
    c0v
    c0v
    chil
    ax-hv0cl
    elexi
    elsn2
    bitri
end
