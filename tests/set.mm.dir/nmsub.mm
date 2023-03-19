include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "cgrp.mm"
include "wceq.mm"
include "simp1.mm"
include "ngpgrp.mm"
include "syl.mm"
include "simp3.mm"
include "simp2.mm"
include "eqid.mm"
include "grpinvsub.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "grpsubcl.mm"
include "nminv.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem nmsub
  let cA: class A
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmmtri.m: |- .- = ( -g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( N ` ( A .- B ) ) = ( N ` ( B .- A ) ) )

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
    cB
    cA
    c.mi
    co
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cN
    cfv
    #
    cA
    cB
    c.mi
    co
    #
    cN
    cfv
    @4
    cN
    cfv
    #
    @3
    @6
    @8
    cN
    @3
    cG
    cgrp
    wcel
    #
    @2
    @1
    @6
    @8
    wceq
    @3
    @0
    @10
    @0
    @1
    @2
    simp1
    #
    cG
    ngpgrp
    syl
    #
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp2
    #
    cX
    cG
    c.mi
    @5
    cB
    cA
    nmf.x
    nmmtri.m
    @5
    eqid
    #
    grpinvsub
    syl3anc
    fveq2d
    @3
    @0
    @4
    cX
    wcel
    #
    @7
    @9
    wceq
    @11
    @3
    @10
    @2
    @1
    @16
    @12
    @13
    @14
    cX
    cG
    c.mi
    cB
    cA
    nmf.x
    nmmtri.m
    grpsubcl
    syl3anc
    @4
    cG
    @5
    cN
    cX
    nmf.x
    nmf.n
    @15
    nminv
    syl2anc
    eqtr3d
end
