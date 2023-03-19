include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cmnd.mm"
include "cbs.mm"
include "wss.mm"
include "c0g.mm"
include "wceq.mm"
include "submrcl.mm"
include "submmnd.mm"
include "eqid.mm"
include "submss.mm"
include "subm0cl.mm"
include "submnd0.mm"
include "syl22anc.mm"

theorem subm0
  let cS: class S
  let cH: class H
  let cM: class M
  let c.0: class .0.
  assume submmnd.h: |- H = ( M |`s S )
  assume subm0.z: |- .0. = ( 0g ` M )


  assert |- ( S e. ( SubMnd ` M ) -> .0. = ( 0g ` H ) )

  proof
    cS
    cM
    csubmnd
    cfv
    wcel
    cM
    cmnd
    wcel
    cH
    cmnd
    wcel
    cS
    cM
    cbs
    cfv
    #
    wss
    c.0
    cS
    wcel
    c.0
    cH
    c0g
    cfv
    wceq
    cS
    cM
    submrcl
    cS
    cH
    cM
    submmnd.h
    submmnd
    @0
    cS
    cM
    @0
    eqid
    #
    submss
    cS
    cM
    c.0
    subm0.z
    subm0cl
    @0
    cS
    cM
    cH
    c.0
    @1
    subm0.z
    submmnd.h
    submnd0
    syl22anc
end
