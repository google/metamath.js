include "ch0o.mm"
include "chod.mm"
include "co.mm"
include "chos.mm"
include "wceq.mm"
include "ho0f.mm"
include "hosubcli.mm"
include "hoaddcli.mm"
include "hoaddcomi.mm"
include "hoaddsubassi.mm"
include "eqtr4i.mm"
include "hoaddid1i.mm"
include "oveq1i.mm"
include "hoaddsubi.mm"
include "hodseqi.mm"
include "3eqtri.mm"
include "hodsi.mm"
include "mpbir.mm"
include "eqcomi.mm"

theorem hosd1i
  let cT: class T
  let cU: class U
  assume hosd1.2: |- T : ~H --> ~H
  assume hosd1.3: |- U : ~H --> ~H


  assert |- ( T +op U ) = ( T -op ( 0hop -op U ) )

  proof
    cT
    ch0o
    cU
    chod
    co
    #
    chod
    co
    #
    cT
    cU
    chos
    co
    #
    @1
    @2
    wceq
    @0
    @2
    chos
    co
    #
    cT
    wceq
    @3
    @2
    ch0o
    chos
    co
    #
    cU
    chod
    co
    #
    @2
    cU
    chod
    co
    #
    cT
    @3
    @2
    @0
    chos
    co
    @5
    @0
    @2
    ch0o
    cU
    ho0f
    hosd1.3
    hosubcli
    #
    cT
    cU
    hosd1.2
    hosd1.3
    hoaddcli
    #
    hoaddcomi
    @2
    ch0o
    cU
    @8
    ho0f
    hosd1.3
    hoaddsubassi
    eqtr4i
    @4
    @2
    cU
    chod
    @2
    @8
    hoaddid1i
    oveq1i
    @6
    cT
    cU
    chod
    co
    #
    cU
    chos
    co
    cU
    @9
    chos
    co
    cT
    cT
    cU
    cU
    hosd1.2
    hosd1.3
    hosd1.3
    hoaddsubi
    @9
    cU
    cT
    cU
    hosd1.2
    hosd1.3
    hosubcli
    hosd1.3
    hoaddcomi
    cU
    cT
    hosd1.3
    hosd1.2
    hodseqi
    3eqtri
    3eqtri
    cT
    @0
    @2
    hosd1.2
    @7
    @8
    hodsi
    mpbir
    eqcomi
end
