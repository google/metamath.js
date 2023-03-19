include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "cds.mm"
include "co.mm"
include "csg.mm"
include "wceq.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "adantr.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "ngpdsr.mm"
include "mpd3an3.mm"
include "nmval.mm"
include "adantl.mm"
include "grpinvval2.mm"
include "sylan.mm"
include "fveq2d.mm"
include "3eqtr4rd.mm"

theorem nminv
  let cA: class A
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nminv.i: |- I = ( invg ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X ) -> ( N ` ( I ` A ) ) = ( N ` A ) )

  proof
    cG
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cG
    c0g
    cfv
    #
    cG
    cds
    cfv
    #
    co
    #
    @3
    cA
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
    cA
    cI
    cfv
    #
    cN
    cfv
    @0
    @1
    @3
    cX
    wcel
    #
    @5
    @8
    wceq
    @2
    cG
    cgrp
    wcel
    #
    @11
    @0
    @12
    @1
    cG
    ngpgrp
    #
    adantr
    cX
    cG
    @3
    nmf.x
    @3
    eqid
    #
    grpidcl
    syl
    cA
    @3
    @4
    cG
    @6
    cN
    cX
    nmf.n
    nmf.x
    @6
    eqid
    #
    @4
    eqid
    #
    ngpdsr
    mpd3an3
    @1
    @9
    @5
    wceq
    @0
    cA
    @4
    cN
    cG
    cX
    @3
    nmf.n
    nmf.x
    @14
    @16
    nmval
    adantl
    @2
    @10
    @7
    cN
    @0
    @12
    @1
    @10
    @7
    wceq
    @13
    cX
    cG
    @6
    cI
    cA
    @3
    nmf.x
    @15
    nminv.i
    @14
    grpinvval2
    sylan
    fveq2d
    3eqtr4rd
end
