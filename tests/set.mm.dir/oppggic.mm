include "cgrp.mm"
include "wcel.mm"
include "cminusg.mm"
include "cfv.mm"
include "cgim.mm"
include "co.mm"
include "cgic.mm"
include "wbr.mm"
include "eqid.mm"
include "invoppggim.mm"
include "brgici.mm"
include "syl.mm"

theorem oppggic
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cZ: class Z
  assume oppggic.o: |- O = ( oppG ` G )


  assert |- ( G e. Grp -> G ~=g O )

  proof
    cG
    cgrp
    wcel
    cG
    cminusg
    cfv
    #
    cG
    cO
    cgim
    co
    wcel
    cG
    cO
    cgic
    wbr
    cG
    @0
    cO
    oppggic.o
    @0
    eqid
    invoppggim
    cG
    cO
    @0
    brgici
    syl
end
