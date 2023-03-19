include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cnmoo.mm"
include "co.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "eqid.mm"
include "isblo.mm"
include "simprbda.mm"
include "3impa.mm"

theorem bloln
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cW: class W
  assume bloln.4: |- L = ( U LnOp W )
  assume bloln.5: |- B = ( U BLnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> T e. L )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cB
    wcel
    #
    cT
    cL
    wcel
    #
    @0
    @1
    wa
    @2
    @3
    cT
    cU
    cW
    cnmoo
    co
    #
    cfv
    cpnf
    clt
    wbr
    cB
    cT
    cU
    cL
    @4
    cW
    @4
    eqid
    bloln.4
    bloln.5
    isblo
    simprbda
    3impa
end
