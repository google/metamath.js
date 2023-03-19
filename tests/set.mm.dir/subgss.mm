include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "issubg.mm"
include "simp2bi.mm"

theorem subgss
  let cB: class B
  let cS: class S
  let cG: class G
  let vs: setvar s
  let vw: setvar w
  assume issubg.b: |- B = ( Base ` G )


  assert |- ( S e. ( SubGrp ` G ) -> S C_ B )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    cG
    cgrp
    wcel
    cS
    cB
    wss
    cG
    cS
    cress
    co
    cgrp
    wcel
    cB
    cS
    cG
    issubg.b
    issubg
    simp2bi
end
