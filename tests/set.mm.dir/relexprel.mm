include "wrel.mm"
include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "crelexp.mm"
include "co.mm"
include "ax-1.mm"
include "relexprelg.mm"
include "syl3an3.mm"

theorem relexprel
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN0 /\ R e. V /\ Rel R ) -> Rel ( R ^r N ) )

  proof
    cR
    wrel
    #
    cN
    cn0
    wcel
    cR
    cV
    wcel
    cN
    c1
    wceq
    #
    @0
    wi
    cR
    cN
    crelexp
    co
    wrel
    @0
    @1
    ax-1
    cR
    cN
    cV
    relexprelg
    syl3an3
end
