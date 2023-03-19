include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "issubg.mm"
include "simp3bi.mm"
include "syl5eqel.mm"

theorem subggrp
  let cS: class S
  let cG: class G
  let cH: class H
  assume subggrp.h: |- H = ( G |`s S )


  assert |- ( S e. ( SubGrp ` G ) -> H e. Grp )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cH
    cG
    cS
    cress
    co
    #
    cgrp
    subggrp.h
    @0
    cG
    cgrp
    wcel
    cS
    cG
    cbs
    cfv
    #
    wss
    @1
    cgrp
    wcel
    @2
    cS
    cG
    @2
    eqid
    issubg
    simp3bi
    syl5eqel
end
