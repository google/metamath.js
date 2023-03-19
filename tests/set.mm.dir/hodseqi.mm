include "chod.mm"
include "co.mm"
include "wceq.mm"
include "chos.mm"
include "eqid.mm"
include "hosubcli.mm"
include "hodsi.mm"
include "mpbi.mm"

theorem hodseqi
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hodseq.2: |- S : ~H --> ~H
  assume hodseq.3: |- T : ~H --> ~H


  assert |- ( S +op ( T -op S ) ) = T

  proof
    cT
    cS
    chod
    co
    #
    @0
    wceq
    cS
    @0
    chos
    co
    cT
    wceq
    @0
    eqid
    cT
    cS
    @0
    hodseq.3
    hodseq.2
    cT
    cS
    hodseq.3
    hodseq.2
    hosubcli
    hodsi
    mpbi
end
