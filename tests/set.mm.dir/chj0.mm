include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "chj0i.mm"
include "dedth.mm"

theorem chj0
  let cA: class A


  assert |- ( A e. CH -> ( A vH 0H ) = A )

  proof
    cA
    cch
    wcel
    #
    cA
    c0h
    chj
    co
    #
    cA
    wceq
    @0
    cA
    c0h
    cif
    #
    c0h
    chj
    co
    #
    @2
    wceq
    cA
    c0h
    cA
    @2
    wceq
    #
    @1
    @3
    cA
    @2
    cA
    @2
    c0h
    chj
    oveq1
    @4
    id
    eqeq12d
    @2
    cA
    c0h
    cch
    h0elch
    elimel
    chj0i
    dedth
end
