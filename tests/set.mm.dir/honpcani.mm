include "chos.mm"
include "co.mm"
include "chod.mm"
include "hoaddsubi.mm"
include "hopncani.mm"
include "eqtr3i.mm"

theorem honpcani
  let cT: class T
  let cU: class U
  assume hosd1.2: |- T : ~H --> ~H
  assume hosd1.3: |- U : ~H --> ~H


  assert |- ( ( T -op U ) +op U ) = T

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
    chod
    co
    cU
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
    cT
    cU
    hosd1.2
    hosd1.3
    hopncani
    eqtr3i
end
