include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "submgmss.mm"
include "ressbas2.mm"
include "syl.mm"

theorem submgmbas
  let cS: class S
  let cH: class H
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume submgmmgm.h: |- H = ( M |`s S )


  assert |- ( S e. ( SubMgm ` M ) -> S = ( Base ` H ) )

  proof
    cS
    cM
    csubmgm
    cfv
    wcel
    cS
    cM
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
    cM
    @0
    eqid
    #
    submgmss
    cS
    @0
    cH
    cM
    submgmmgm.h
    @1
    ressbas2
    syl
end
