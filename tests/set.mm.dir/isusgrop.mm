include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cusgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "eqid.mm"
include "isusgrs.mm"
include "mp1i.mm"
include "opiedgfv.mm"
include "dmeqd.mm"
include "opvtxfv.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "f1eq123d.mm"
include "bitrd.mm"

theorem isusgrop
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let vp: setvar p

  disjoint E p
  disjoint V p
  disjoint W p
  disjoint X p
  assert |- ( ( V e. W /\ E e. X ) -> ( <. V , E >. e. USGraph <-> E : dom E -1-1-> { p e. ~P V | ( # ` p ) = 2 } ) )

  proof
    cV
    cW
    wcel
    cE
    cX
    wcel
    wa
    #
    cV
    cE
    cop
    #
    cusgr
    wcel
    #
    @1
    ciedg
    cfv
    #
    cdm
    #
    vp
    cv
    chash
    cfv
    c2
    wceq
    #
    vp
    @1
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @3
    wf1
    #
    cE
    cdm
    #
    @5
    vp
    cV
    cpw
    #
    crab
    #
    cE
    wf1
    @1
    cvv
    wcel
    @2
    @9
    wb
    @0
    cV
    cE
    opex
    vp
    cvv
    @3
    @1
    @6
    @6
    eqid
    @3
    eqid
    isusgrs
    mp1i
    @0
    @4
    @10
    @8
    @12
    @3
    cE
    cE
    cV
    cW
    cX
    opiedgfv
    #
    @0
    @3
    cE
    @13
    dmeqd
    @0
    @5
    vp
    @7
    @11
    @0
    @6
    cV
    cE
    cV
    cW
    cX
    opvtxfv
    pweqd
    rabeqdv
    f1eq123d
    bitrd
end
