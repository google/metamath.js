include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0g.mm"
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
include "simp1d.mm"

theorem submss
  let cB: class B
  let cS: class S
  let cM: class M
  assume submss.b: |- B = ( Base ` M )


  assert |- ( S e. ( SubMnd ` M ) -> S C_ B )

  proof
    cS
    cM
    csubmnd
    cfv
    wcel
    #
    cS
    cB
    wss
    #
    cM
    c0g
    cfv
    #
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
    @1
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
    cB
    cS
    @4
    cM
    @2
    submss.b
    @2
    eqid
    @4
    eqid
    issubm2
    syl
    ibi
    simp1d
end
