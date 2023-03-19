include "chom.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "1nn0.mm"
include "4nn.mm"
include "decnncl.mm"
include "1nn.mm"
include "4nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "resslem.mm"

theorem resshom
  let cA: class A
  let cC: class C
  let cD: class D
  let cH: class H
  let cV: class V
  assume resshom.1: |- D = ( C |`s A )
  assume resshom.2: |- H = ( Hom ` C )


  assert |- ( A e. V -> H = ( Hom ` D ) )

  proof
    cA
    cH
    cD
    chom
    c1
    c4
    cdc
    cV
    cC
    resshom.1
    resshom.2
    df-hom
    c1
    c4
    1nn0
    4nn
    decnncl
    c1
    c4
    c1
    1nn
    4nn0
    1nn0
    1lt10
    declti
    resslem
end
