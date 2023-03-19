include "chos.mm"
include "co.mm"
include "chod.mm"
include "ch0o.mm"
include "hoaddsubassi.mm"
include "hodidi.mm"
include "oveq2i.mm"
include "hoaddid1i.mm"
include "3eqtri.mm"

theorem hopncani
  let cT: class T
  let cU: class U
  assume hosd1.2: |- T : ~H --> ~H
  assume hosd1.3: |- U : ~H --> ~H


  assert |- ( ( T +op U ) -op U ) = T

  proof
    cT
    cU
    chos
    co
    cU
    chod
    co
    cT
    cU
    cU
    chod
    co
    #
    chos
    co
    cT
    ch0o
    chos
    co
    cT
    cT
    cU
    cU
    hosd1.2
    hosd1.3
    hosd1.3
    hoaddsubassi
    @0
    ch0o
    cT
    chos
    cU
    hosd1.3
    hodidi
    oveq2i
    cT
    hosd1.2
    hoaddid1i
    3eqtri
end
