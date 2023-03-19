include "cco.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "df-cco.mm"
include "1nn0.mm"
include "5nn.mm"
include "decnncl.mm"
include "1nn.mm"
include "5nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "resslem.mm"

theorem ressco
  let cA: class A
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let cV: class V
  assume resshom.1: |- D = ( C |`s A )
  assume ressco.2: |- .x. = ( comp ` C )


  assert |- ( A e. V -> .x. = ( comp ` D ) )

  proof
    cA
    c.x
    cD
    cco
    c1
    c5
    cdc
    cV
    cC
    resshom.1
    ressco.2
    df-cco
    c1
    c5
    1nn0
    5nn
    decnncl
    c1
    c5
    c1
    1nn
    5nn0
    1nn0
    1lt10
    declti
    resslem
end
