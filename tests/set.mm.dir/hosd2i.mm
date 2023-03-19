include "chos.mm"
include "co.mm"
include "ch0o.mm"
include "chod.mm"
include "hosd1i.mm"
include "hodidi.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "eqtr4i.mm"

theorem hosd2i
  let cT: class T
  let cU: class U
  assume hosd1.2: |- T : ~H --> ~H
  assume hosd1.3: |- U : ~H --> ~H


  assert |- ( T +op U ) = ( T -op ( ( U -op U ) -op U ) )

  proof
    cT
    cU
    chos
    co
    cT
    ch0o
    cU
    chod
    co
    #
    chod
    co
    cT
    cU
    cU
    chod
    co
    #
    cU
    chod
    co
    #
    chod
    co
    cT
    cU
    hosd1.2
    hosd1.3
    hosd1i
    @2
    @0
    cT
    chod
    @1
    ch0o
    cU
    chod
    cU
    hosd1.3
    hodidi
    oveq1i
    oveq2i
    eqtr4i
end
