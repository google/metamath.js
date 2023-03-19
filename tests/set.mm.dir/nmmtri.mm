include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "cds.mm"
include "cfv.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "eqid.mm"
include "ngpds.mm"
include "c0g.mm"
include "cmt.mm"
include "wbr.mm"
include "ngpms.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "mstri3.mm"
include "syl13anc.mm"
include "wceq.mm"
include "nmval.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "oveq12d.mm"
include "breqtrrd.mm"
include "eqbrtrrd.mm"

theorem nmmtri
  let cA: class A
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmmtri.m: |- .- = ( -g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( N ` ( A .- B ) ) <_ ( ( N ` A ) + ( N ` B ) ) )

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
    cds
    cfv
    #
    co
    #
    cA
    cB
    c.mi
    co
    cN
    cfv
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    caddc
    co
    #
    cle
    cA
    cB
    @4
    cG
    c.mi
    cN
    cX
    nmf.n
    nmf.x
    nmmtri.m
    @4
    eqid
    #
    ngpds
    @3
    @5
    cA
    cG
    c0g
    cfv
    #
    @4
    co
    #
    cB
    @10
    @4
    co
    #
    caddc
    co
    #
    @8
    cle
    @3
    cG
    cmt
    wcel
    #
    @1
    @2
    @10
    cX
    wcel
    #
    @5
    @13
    cle
    wbr
    @0
    @1
    @14
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
    @0
    @1
    @15
    @2
    @0
    cG
    cgrp
    wcel
    @15
    cG
    ngpgrp
    cX
    cG
    @10
    nmf.x
    @10
    eqid
    #
    grpidcl
    syl
    3ad2ant1
    cA
    cB
    @10
    @4
    cG
    cX
    nmf.x
    @9
    mstri3
    syl13anc
    @3
    @6
    @11
    @7
    @12
    caddc
    @1
    @0
    @6
    @11
    wceq
    @2
    cA
    @4
    cN
    cG
    cX
    @10
    nmf.n
    nmf.x
    @16
    @9
    nmval
    3ad2ant2
    @2
    @0
    @7
    @12
    wceq
    @1
    cB
    @4
    cN
    cG
    cX
    @10
    nmf.n
    nmf.x
    @16
    @9
    nmval
    3ad2ant3
    oveq12d
    breqtrrd
    eqbrtrrd
end
