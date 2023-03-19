include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "subgss.mm"
include "ressbas2.mm"
include "syl.mm"

theorem subgbas
  let cS: class S
  let cG: class G
  let cH: class H
  assume subggrp.h: |- H = ( G |`s S )


  assert |- ( S e. ( SubGrp ` G ) -> S = ( Base ` H ) )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    cS
    cG
    cbs
    cfv
    #
    wss
    cS
    cH
    cbs
    cfv
    wceq
    @0
    cS
    cG
    @0
    eqid
    #
    subgss
    cS
    @0
    cH
    cG
    subggrp.h
    @1
    ressbas2
    syl
end
