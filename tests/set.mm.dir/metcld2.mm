include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "metcld.mm"
include "wex.mm"
include "19.23v.mm"
include "vex.mm"
include "elima2.mm"
include "cvv.mm"
include "wb.mm"
include "cdm.mm"
include "id.mm"
include "elfvdm.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "nnex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5rbb.mm"
include "imbi1d.mm"
include "syl5bb.mm"
include "albidv.mm"
include "dfss2.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem metcld2
  let cD: class D
  let cS: class S
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume metcld.2: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( *Met ` X ) /\ S C_ X ) -> ( S e. ( Clsd ` J ) <-> ( ( ~~>t ` J ) " ( S ^m NN ) ) C_ S ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    ccld
    cfv
    wcel
    cn
    cS
    vf
    cv
    #
    wf
    #
    @3
    vx
    cv
    #
    cJ
    clm
    cfv
    #
    wbr
    #
    wa
    #
    @5
    cS
    wcel
    #
    wi
    vf
    wal
    #
    vx
    wal
    #
    @6
    cS
    cn
    cmap
    co
    #
    cima
    #
    cS
    wss
    #
    vx
    cD
    cS
    vf
    cJ
    cX
    metcld.2
    metcld
    @2
    @11
    @5
    @13
    wcel
    #
    @9
    wi
    #
    vx
    wal
    @14
    @2
    @10
    @16
    vx
    @10
    @8
    vf
    wex
    #
    @9
    wi
    @2
    @16
    @8
    @9
    vf
    19.23v
    @2
    @17
    @15
    @9
    @15
    @3
    @12
    wcel
    #
    @7
    wa
    #
    vf
    wex
    @2
    @17
    vf
    @5
    @6
    @12
    vx
    vex
    elima2
    @2
    @19
    @8
    vf
    @2
    @18
    @4
    @7
    @2
    cS
    cvv
    wcel
    #
    cn
    cvv
    wcel
    @18
    @4
    wb
    @1
    @1
    cX
    cxmt
    cdm
    #
    wcel
    @20
    @0
    @1
    id
    cD
    cX
    cxmt
    elfvdm
    cS
    cX
    @21
    ssexg
    syl2anr
    nnex
    cS
    cn
    @3
    cvv
    cvv
    elmapg
    sylancl
    anbi1d
    exbidv
    syl5rbb
    imbi1d
    syl5bb
    albidv
    vx
    @13
    cS
    dfss2
    syl6bbr
    bitrd
end
