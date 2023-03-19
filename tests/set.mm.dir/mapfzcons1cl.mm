include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "wss.mm"
include "cres.mm"
include "caddc.mm"
include "fzssp1.mm"
include "oveq2i.mm"
include "sseqtr4i.mm"
include "elmapssres.mm"
include "mpan2.mm"

theorem mapfzcons1cl
  let cA: class A
  let cB: class B
  let cM: class M
  let cN: class N
  assume mapfzcons.1: |- M = ( N + 1 )


  assert |- ( A e. ( B ^m ( 1 ... M ) ) -> ( A |` ( 1 ... N ) ) e. ( B ^m ( 1 ... N ) ) )

  proof
    cA
    cB
    c1
    cM
    cfz
    co
    #
    cmap
    co
    wcel
    c1
    cN
    cfz
    co
    #
    @0
    wss
    cA
    @1
    cres
    cB
    @1
    cmap
    co
    wcel
    @1
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    @0
    c1
    cN
    fzssp1
    cM
    @2
    c1
    cfz
    mapfzcons.1
    oveq2i
    sseqtr4i
    cA
    cB
    @0
    @1
    elmapssres
    mpan2
end
