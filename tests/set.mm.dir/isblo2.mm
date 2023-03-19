include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "isblo.mm"
include "wb.mm"
include "cba.mm"
include "wf.mm"
include "eqid.mm"
include "lnof.mm"
include "nmoreltpnf.mm"
include "syld3an3.mm"
include "3expa.mm"
include "pm5.32da.mm"
include "bitr4d.mm"

theorem isblo2
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cW: class W
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  assume bloval.3: |- N = ( U normOpOLD W )
  assume bloval.4: |- L = ( U LnOp W )
  assume bloval.5: |- B = ( U BLnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <-> ( T e. L /\ ( N ` T ) e. RR ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    wa
    #
    cT
    cB
    wcel
    cT
    cL
    wcel
    #
    cT
    cN
    cfv
    #
    cpnf
    clt
    wbr
    #
    wa
    @3
    @4
    cr
    wcel
    #
    wa
    cB
    cT
    cU
    cL
    cN
    cW
    bloval.3
    bloval.4
    bloval.5
    isblo
    @2
    @3
    @6
    @5
    @0
    @1
    @3
    @6
    @5
    wb
    #
    @0
    @1
    @3
    cU
    cba
    cfv
    #
    cW
    cba
    cfv
    #
    cT
    wf
    @7
    cT
    cU
    cL
    cW
    @8
    @9
    @8
    eqid
    #
    @9
    eqid
    #
    bloval.4
    lnof
    cT
    cU
    cN
    cW
    @8
    @9
    @10
    @11
    bloval.3
    nmoreltpnf
    syld3an3
    3expa
    pm5.32da
    bitr4d
end
