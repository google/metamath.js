include "c1.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "fzssp1.mm"
include "oveq2i.mm"
include "sseqtr4i.mm"
include "sstri.mm"

theorem jm2.27dlem5
  let cA: class A
  let cB: class B
  let cC: class C
  assume jm2.27dlem5.2: |- B = ( A + 1 )
  assume jm2.27dlem5.3: |- ( 1 ... B ) C_ ( 1 ... C )


  assert |- ( 1 ... A ) C_ ( 1 ... C )

  proof
    c1
    cA
    cfz
    co
    #
    c1
    cB
    cfz
    co
    #
    c1
    cC
    cfz
    co
    @0
    c1
    cA
    c1
    caddc
    co
    #
    cfz
    co
    @1
    c1
    cA
    fzssp1
    cB
    @2
    c1
    cfz
    jm2.27dlem5.2
    oveq2i
    sseqtr4i
    jm2.27dlem5.3
    sstri
end
