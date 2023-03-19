include "chod.mm"
include "co.mm"
include "ch0o.mm"
include "chos.mm"
include "wceq.mm"
include "ho0f.mm"
include "hosubcli.mm"
include "hoadd12i.mm"
include "hodseqi.mm"
include "oveq2i.mm"
include "hoaddid1i.mm"
include "3eqtri.mm"
include "hoaddcli.mm"
include "hodsi.mm"
include "mpbir.mm"

theorem ho0subi
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hodseq.2: |- S : ~H --> ~H
  assume hodseq.3: |- T : ~H --> ~H


  assert |- ( S -op T ) = ( S +op ( 0hop -op T ) )

  proof
    cS
    cT
    chod
    co
    cS
    ch0o
    cT
    chod
    co
    #
    chos
    co
    #
    wceq
    cT
    @1
    chos
    co
    #
    cS
    wceq
    @2
    cS
    cT
    @0
    chos
    co
    #
    chos
    co
    cS
    ch0o
    chos
    co
    cS
    cT
    cS
    @0
    hodseq.3
    hodseq.2
    ch0o
    cT
    ho0f
    hodseq.3
    hosubcli
    #
    hoadd12i
    @3
    ch0o
    cS
    chos
    cT
    ch0o
    hodseq.3
    ho0f
    hodseqi
    oveq2i
    cS
    hodseq.2
    hoaddid1i
    3eqtri
    cS
    cT
    @1
    hodseq.2
    hodseq.3
    cS
    @0
    hodseq.2
    @4
    hoaddcli
    hodsi
    mpbir
end
