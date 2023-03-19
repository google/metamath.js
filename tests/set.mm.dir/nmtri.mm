include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "cminusg.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "nmmtri.mm"
include "syld3an3.mm"
include "simp2.mm"
include "grpsubinv.mm"
include "fveq2d.mm"
include "wceq.mm"
include "nminv.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "3brtr3d.mm"

theorem nmtri
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmtri.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( N ` ( A .+ B ) ) <_ ( ( N ` A ) + ( N ` B ) ) )

  proof
    cG
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    @5
    cN
    cfv
    #
    caddc
    co
    #
    cA
    cB
    c.pl
    co
    #
    cN
    cfv
    @9
    cB
    cN
    cfv
    #
    caddc
    co
    cle
    @0
    @1
    @2
    @5
    cX
    wcel
    #
    @8
    @11
    cle
    wbr
    @3
    cG
    cgrp
    wcel
    #
    @2
    @14
    @0
    @1
    @15
    @2
    cG
    ngpgrp
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    cX
    cG
    @4
    cB
    nmf.x
    @4
    eqid
    #
    grpinvcl
    syl2anc
    cA
    @5
    cG
    @6
    cN
    cX
    nmf.x
    nmf.n
    @6
    eqid
    #
    nmmtri
    syld3an3
    @3
    @7
    @12
    cN
    @3
    cX
    c.pl
    cG
    @6
    @4
    cA
    cB
    nmf.x
    nmtri.p
    @19
    @18
    @16
    @0
    @1
    @2
    simp2
    @17
    grpsubinv
    fveq2d
    @3
    @10
    @13
    @9
    caddc
    @0
    @2
    @10
    @13
    wceq
    @1
    cB
    cG
    @4
    cN
    cX
    nmf.x
    nmf.n
    @18
    nminv
    3adant2
    oveq2d
    3brtr3d
end
