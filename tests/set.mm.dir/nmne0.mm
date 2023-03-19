include "cngp.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "nmeq0.mm"
include "necon3bid.mm"
include "biimp3ar.mm"

theorem nmne0
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmeq0.z: |- .0. = ( 0g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ A =/= .0. ) -> ( N ` A ) =/= 0 )

  proof
    cG
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cN
    cfv
    #
    cc0
    wne
    cA
    c.0
    wne
    @0
    @1
    wa
    @2
    cc0
    cA
    c.0
    cA
    cG
    cN
    cX
    c.0
    nmf.x
    nmf.n
    nmeq0.z
    nmeq0
    necon3bid
    biimp3ar
end
