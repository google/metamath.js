include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "submss.mm"
include "ressbas2.mm"
include "syl.mm"

theorem submbas
  let cS: class S
  let cH: class H
  let cM: class M
  assume submmnd.h: |- H = ( M |`s S )


  assert |- ( S e. ( SubMnd ` M ) -> S = ( Base ` H ) )

  proof
    cS
    cM
    csubmnd
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
    submss
    cS
    @0
    cH
    cM
    submmnd.h
    @1
    ressbas2
    syl
end
