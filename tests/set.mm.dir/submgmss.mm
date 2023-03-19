include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "cmgm.mm"
include "wa.mm"
include "wb.mm"
include "submgmrcl.mm"
include "eqid.mm"
include "issubmgm2.mm"
include "syl.mm"
include "ibi.mm"
include "simpld.mm"

theorem submgmss
  let cB: class B
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume submgmss.b: |- B = ( Base ` M )


  assert |- ( S e. ( SubMgm ` M ) -> S C_ B )

  proof
    cS
    cM
    csubmgm
    cfv
    wcel
    #
    cS
    cB
    wss
    #
    cM
    cS
    cress
    co
    #
    cmgm
    wcel
    #
    @0
    @1
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
    cB
    cS
    @2
    cM
    submgmss.b
    @2
    eqid
    issubmgm2
    syl
    ibi
    simpld
end
