include "cds.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "df-ds.mm"
include "1nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "1nn.mm"
include "2nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "resslem.mm"

theorem ressds
  let cA: class A
  let cD: class D
  let cG: class G
  let cH: class H
  let cV: class V
  assume ressds.1: |- H = ( G |`s A )
  assume ressds.2: |- D = ( dist ` G )


  assert |- ( A e. V -> D = ( dist ` H ) )

  proof
    cA
    cD
    cH
    cds
    c1
    c2
    cdc
    cV
    cG
    ressds.1
    ressds.2
    df-ds
    c1
    c2
    1nn0
    2nn
    decnncl
    c1
    c2
    c1
    1nn
    2nn0
    1nn0
    1lt10
    declti
    resslem
end
