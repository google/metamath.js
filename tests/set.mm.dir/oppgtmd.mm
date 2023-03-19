include "ctmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctps.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "ctopn.mm"
include "ctx.mm"
include "ccn.mm"
include "tmdmnd.mm"
include "oppgmnd.mm"
include "syl.mm"
include "ctopon.mm"
include "eqid.mm"
include "tmdtopon.mm"
include "oppgbas.mm"
include "oppgtopn.mm"
include "istps.mm"
include "sylibr.mm"
include "id.mm"
include "cnmpt2nd.mm"
include "cnmpt1st.mm"
include "cnmpt2plusg.mm"
include "cplusf.mm"
include "plusffval.mm"
include "oppgplus.mm"
include "mpt2eq123i.mm"
include "eqtr2i.mm"
include "istmd.mm"
include "syl3anbrc.mm"

theorem oppgtmd
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume oppgtmd.1: |- O = ( oppG ` G )


  assert |- ( G e. TopMnd -> O e. TopMnd )

  proof
    cG
    ctmd
    wcel
    #
    cO
    cmnd
    wcel
    #
    cO
    ctps
    wcel
    #
    vx
    vy
    cG
    cbs
    cfv
    #
    @3
    vy
    cv
    #
    vx
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    cG
    ctopn
    cfv
    #
    @9
    ctx
    co
    @9
    ccn
    co
    wcel
    cO
    ctmd
    wcel
    @0
    cG
    cmnd
    wcel
    @1
    cG
    tmdmnd
    cG
    cO
    oppgtmd.1
    oppgmnd
    syl
    @0
    @9
    @3
    ctopon
    cfv
    wcel
    @2
    cG
    @9
    @3
    @9
    eqid
    #
    @3
    eqid
    #
    tmdtopon
    #
    @3
    @9
    cO
    @3
    cG
    cO
    oppgtmd.1
    @11
    oppgbas
    #
    cG
    @9
    cO
    oppgtmd.1
    @10
    oppgtopn
    #
    istps
    sylibr
    @0
    vx
    vy
    @4
    @5
    @6
    cG
    @9
    @9
    @9
    @3
    @3
    @10
    @6
    eqid
    #
    @0
    id
    @12
    @12
    @0
    vx
    vy
    @9
    @9
    @3
    @3
    @12
    @12
    cnmpt2nd
    @0
    vx
    vy
    @9
    @9
    @3
    @3
    @12
    @12
    cnmpt1st
    cnmpt2plusg
    @8
    cO
    @9
    cO
    cplusf
    cfv
    #
    vx
    vy
    @3
    @3
    @5
    @4
    cO
    cplusg
    cfv
    #
    co
    #
    cmpt2
    @8
    vx
    vy
    @3
    @17
    @16
    cO
    @13
    @17
    eqid
    #
    @16
    eqid
    plusffval
    vx
    vy
    @3
    @3
    @18
    @3
    @3
    @7
    @11
    @11
    @6
    @17
    cG
    cO
    @5
    @4
    @15
    oppgtmd.1
    @19
    oppgplus
    mpt2eq123i
    eqtr2i
    @14
    istmd
    syl3anbrc
end
