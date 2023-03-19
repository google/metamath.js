include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "eqid.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "clmod.mm"
include "wb.mm"
include "islsat.mm"
include "syl.mm"
include "mpbird.mm"

theorem lsatlspsn
  let wph: wff ph
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
  assume lsatlspsn.w: |- ( ph -> W e. LMod )
  assume lsatlspsn.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( N ` { X } ) e. A )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    cA
    wcel
    #
    @1
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
    wph
    cX
    @7
    wcel
    @1
    @1
    wceq
    #
    @8
    lsatlspsn.x
    @1
    eqid
    @6
    @9
    vv
    cX
    @7
    @3
    cX
    wceq
    #
    @5
    @1
    @1
    @10
    @4
    @0
    cN
    @3
    cX
    sneq
    fveq2d
    eqeq2d
    rspcev
    sylancl
    wph
    cW
    clmod
    wcel
    @2
    @8
    wb
    lsatlspsn.w
    vv
    cA
    @1
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
    syl
    mpbird
end
