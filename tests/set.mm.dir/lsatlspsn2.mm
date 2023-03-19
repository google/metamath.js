include "clmod.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "wa.mm"
include "3simpc.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "eqid.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wb.mm"
include "islsat.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem lsatlspsn2
  let cA: class A
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cU: class U
  assume lsatset.v: |- V = ( Base ` W )
  assume lsatset.n: |- N = ( LSpan ` W )
  assume lsatset.z: |- .0. = ( 0g ` W )
  assume lsatset.a: |- A = ( LSAtoms ` W )


  assert |- ( ( W e. LMod /\ X e. V /\ X =/= .0. ) -> ( N ` { X } ) e. A )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    c.0
    wne
    #
    w3a
    #
    cX
    csn
    #
    cN
    cfv
    #
    cA
    wcel
    #
    @5
    vv
    cv
    #
    csn
    #
    cN
    cfv
    #
    wceq
    #
    vv
    cV
    c.0
    csn
    cdif
    #
    wrex
    #
    @3
    cX
    @11
    wcel
    #
    @5
    @5
    wceq
    #
    @12
    @3
    @1
    @2
    wa
    @13
    @0
    @1
    @2
    3simpc
    cX
    cV
    c.0
    eldifsn
    sylibr
    @5
    eqid
    @10
    @14
    vv
    cX
    @11
    @7
    cX
    wceq
    #
    @9
    @5
    @5
    @15
    @8
    @4
    cN
    @7
    cX
    sneq
    fveq2d
    eqeq2d
    rspcev
    sylancl
    @0
    @1
    @6
    @12
    wb
    @2
    vv
    cA
    @5
    cN
    cV
    cW
    clmod
    c.0
    lsatset.v
    lsatset.n
    lsatset.z
    lsatset.a
    islsat
    3ad2ant1
    mpbird
end
