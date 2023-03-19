include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "c0g.mm"
include "cfv.mm"
include "cds.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "cmt.mm"
include "wbr.mm"
include "ngpms.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "msrtri.mm"
include "syl13anc.mm"
include "wceq.mm"
include "nmval.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "ngpds.mm"
include "eqcomd.mm"
include "3brtr4d.mm"

theorem nmrtri
  let cA: class A
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmmtri.m: |- .- = ( -g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( abs ` ( ( N ` A ) - ( N ` B ) ) ) <_ ( N ` ( A .- B ) ) )

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
    cB
    @4
    @5
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    cB
    @5
    co
    #
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    cA
    cB
    c.mi
    co
    cN
    cfv
    #
    cle
    @3
    cG
    cmt
    wcel
    #
    @1
    @2
    @4
    cX
    wcel
    #
    @9
    @10
    cle
    wbr
    @0
    @1
    @15
    @2
    cG
    ngpms
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    cG
    cgrp
    wcel
    #
    @16
    @0
    @1
    @17
    @2
    cG
    ngpgrp
    3ad2ant1
    cX
    cG
    @4
    nmf.x
    @4
    eqid
    #
    grpidcl
    syl
    cA
    cB
    @4
    @5
    cG
    cX
    nmf.x
    @5
    eqid
    #
    msrtri
    syl13anc
    @3
    @13
    @8
    cabs
    @3
    @11
    @6
    @12
    @7
    cmin
    @1
    @0
    @11
    @6
    wceq
    @2
    cA
    @5
    cN
    cG
    cX
    @4
    nmf.n
    nmf.x
    @18
    @19
    nmval
    3ad2ant2
    @2
    @0
    @12
    @7
    wceq
    @1
    cB
    @5
    cN
    cG
    cX
    @4
    nmf.n
    nmf.x
    @18
    @19
    nmval
    3ad2ant3
    oveq12d
    fveq2d
    @3
    @10
    @14
    cA
    cB
    @5
    cG
    c.mi
    cN
    cX
    nmf.n
    nmf.x
    nmmtri.m
    @19
    ngpds
    eqcomd
    3brtr4d
end
