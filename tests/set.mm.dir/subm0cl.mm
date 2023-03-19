include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "cmnd.mm"
include "w3a.mm"
include "wb.mm"
include "submrcl.mm"
include "eqid.mm"
include "issubm2.mm"
include "syl.mm"
include "ibi.mm"
include "simp2d.mm"

theorem subm0cl
  let cS: class S
  let cM: class M
  let c.0: class .0.
  assume subm0cl.z: |- .0. = ( 0g ` M )


  assert |- ( S e. ( SubMnd ` M ) -> .0. e. S )

  proof
    cS
    cM
    csubmnd
    cfv
    wcel
    #
    cS
    cM
    cbs
    cfv
    #
    wss
    #
    c.0
    cS
    wcel
    #
    cM
    cS
    cress
    co
    #
    cmnd
    wcel
    #
    @0
    @2
    @3
    @5
    w3a
    #
    @0
    cM
    cmnd
    wcel
    @0
    @6
    wb
    cS
    cM
    submrcl
    @1
    cS
    @4
    cM
    c.0
    @1
    eqid
    subm0cl.z
    @4
    eqid
    issubm2
    syl
    ibi
    simp2d
end
