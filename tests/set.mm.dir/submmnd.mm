include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "c0g.mm"
include "cmnd.mm"
include "w3a.mm"
include "wb.mm"
include "submrcl.mm"
include "eqid.mm"
include "issubm2.mm"
include "syl.mm"
include "ibi.mm"
include "simp3d.mm"

theorem submmnd
  let cS: class S
  let cH: class H
  let cM: class M
  assume submmnd.h: |- H = ( M |`s S )


  assert |- ( S e. ( SubMnd ` M ) -> H e. Mnd )

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
    cM
    c0g
    cfv
    #
    cS
    wcel
    #
    cH
    cmnd
    wcel
    #
    @0
    @2
    @4
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
    cH
    cM
    @3
    @1
    eqid
    @3
    eqid
    submmnd.h
    issubm2
    syl
    ibi
    simp3d
end
