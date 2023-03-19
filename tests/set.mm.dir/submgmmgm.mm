include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "cmgm.mm"
include "wa.mm"
include "wb.mm"
include "submgmrcl.mm"
include "eqid.mm"
include "issubmgm2.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"

theorem submgmmgm
  let cS: class S
  let cH: class H
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume submgmmgm.h: |- H = ( M |`s S )


  assert |- ( S e. ( SubMgm ` M ) -> H e. Mgm )

  proof
    cS
    cM
    csubmgm
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
    cH
    cmgm
    wcel
    #
    @0
    @2
    @3
    wa
    #
    @0
    cM
    cmgm
    wcel
    @0
    @4
    wb
    cS
    cM
    submgmrcl
    @1
    cS
    cH
    cM
    @1
    eqid
    submgmmgm.h
    issubmgm2
    syl
    ibi
    simprd
end
