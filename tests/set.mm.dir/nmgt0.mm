include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "nmeq0.mm"
include "necon3bid.mm"
include "cr.mm"
include "cle.mm"
include "wb.mm"
include "nmcl.mm"
include "nmge0.mm"
include "ne0gt0.mm"
include "syl2anc.mm"
include "bitr3d.mm"

theorem nmgt0
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume nmgt0.x: |- X = ( Base ` G )
  assume nmgt0.n: |- N = ( norm ` G )
  assume nmgt0.z: |- .0. = ( 0g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X ) -> ( A =/= .0. <-> 0 < ( N ` A ) ) )

  proof
    cG
    cngp
    wcel
    cA
    cX
    wcel
    wa
    #
    cA
    cN
    cfv
    #
    cc0
    wne
    #
    cA
    c.0
    wne
    cc0
    @1
    clt
    wbr
    #
    @0
    @1
    cc0
    cA
    c.0
    cA
    cG
    cN
    cX
    c.0
    nmgt0.x
    nmgt0.n
    nmgt0.z
    nmeq0
    necon3bid
    @0
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @2
    @3
    wb
    cA
    cG
    cN
    cX
    nmgt0.x
    nmgt0.n
    nmcl
    cA
    cG
    cN
    cX
    nmgt0.x
    nmgt0.n
    nmge0
    @1
    ne0gt0
    syl2anc
    bitr3d
end
