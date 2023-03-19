include "cunif.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "df-unif.mm"
include "1nn0.mm"
include "3nn.mm"
include "decnncl.mm"
include "1nn.mm"
include "3nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "resslem.mm"

theorem ressunif
  let cA: class A
  let cU: class U
  let cG: class G
  let cH: class H
  let cV: class V
  assume ressunif.1: |- H = ( G |`s A )
  assume ressunif.2: |- U = ( UnifSet ` G )


  assert |- ( A e. V -> U = ( UnifSet ` H ) )

  proof
    cA
    cU
    cH
    cunif
    c1
    c3
    cdc
    cV
    cG
    ressunif.1
    ressunif.2
    df-unif
    c1
    c3
    1nn0
    3nn
    decnncl
    c1
    c3
    c1
    1nn
    3nn0
    1nn0
    1lt10
    declti
    resslem
end
