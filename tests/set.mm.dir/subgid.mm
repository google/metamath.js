include "cgrp.mm"
include "wcel.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "id.mm"
include "ssid.mm"
include "a1i.mm"
include "ressid.mm"
include "eqeltrd.mm"
include "issubg.mm"
include "syl3anbrc.mm"

theorem subgid
  let cB: class B
  let cG: class G
  let vs: setvar s
  let vw: setvar w
  let cS: class S
  assume issubg.b: |- B = ( Base ` G )


  assert |- ( G e. Grp -> B e. ( SubGrp ` G ) )

  proof
    cG
    cgrp
    wcel
    #
    @0
    cB
    cB
    wss
    #
    cG
    cB
    cress
    co
    #
    cgrp
    wcel
    cB
    cG
    csubg
    cfv
    wcel
    @0
    id
    #
    @1
    @0
    cB
    ssid
    a1i
    @0
    @2
    cG
    cgrp
    cB
    cG
    cgrp
    issubg.b
    ressid
    @3
    eqeltrd
    cB
    cB
    cG
    issubg.b
    issubg
    syl3anbrc
end
