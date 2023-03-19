include "cngp.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "nmcl.mm"
include "3adant3.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nmge0.mm"
include "nmne0.mm"
include "ne0gt0d.mm"
include "elrpd.mm"

theorem nmrpcl
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmeq0.z: |- .0. = ( 0g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ A =/= .0. ) -> ( N ` A ) e. RR+ )

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
    c.0
    wne
    #
    w3a
    #
    cA
    cN
    cfv
    #
    @0
    @1
    @4
    cr
    wcel
    @2
    cA
    cG
    cN
    cX
    nmf.x
    nmf.n
    nmcl
    3adant3
    #
    @3
    @4
    @5
    @0
    @1
    cc0
    @4
    cle
    wbr
    @2
    cA
    cG
    cN
    cX
    nmf.x
    nmf.n
    nmge0
    3adant3
    cA
    cG
    cN
    cX
    c.0
    nmf.x
    nmf.n
    nmeq0.z
    nmne0
    ne0gt0d
    elrpd
end
