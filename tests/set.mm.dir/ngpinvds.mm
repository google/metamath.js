include "cngp.mm"
include "wcel.mm"
include "cabl.mm"
include "wa.mm"
include "cfv.mm"
include "csg.mm"
include "co.mm"
include "cnm.mm"
include "eqid.mm"
include "simplr.mm"
include "simprr.mm"
include "simprl.mm"
include "ablsub2inv.mm"
include "fveq2d.mm"
include "wceq.mm"
include "simpll.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ngpdsr.mm"
include "syl3anc.mm"
include "ngpds.mm"
include "3eqtr4d.mm"

theorem ngpinvds
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cI: class I
  let cX: class X
  assume ngpinvds.x: |- X = ( Base ` G )
  assume ngpinvds.i: |- I = ( invg ` G )
  assume ngpinvds.d: |- D = ( dist ` G )


  assert |- ( ( ( G e. NrmGrp /\ G e. Abel ) /\ ( A e. X /\ B e. X ) ) -> ( ( I ` A ) D ( I ` B ) ) = ( A D B ) )

  proof
    cG
    cngp
    wcel
    #
    cG
    cabl
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    wa
    #
    cB
    cI
    cfv
    #
    cA
    cI
    cfv
    #
    cG
    csg
    cfv
    #
    co
    #
    cG
    cnm
    cfv
    #
    cfv
    #
    cA
    cB
    @9
    co
    #
    @11
    cfv
    #
    @8
    @7
    cD
    co
    #
    cA
    cB
    cD
    co
    #
    @6
    @10
    @13
    @11
    @6
    cX
    cG
    @9
    cI
    cB
    cA
    ngpinvds.x
    @9
    eqid
    #
    ngpinvds.i
    @0
    @1
    @5
    simplr
    @2
    @3
    @4
    simprr
    #
    @2
    @3
    @4
    simprl
    #
    ablsub2inv
    fveq2d
    @6
    @0
    @8
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    @15
    @12
    wceq
    @0
    @1
    @5
    simpll
    #
    @6
    cG
    cgrp
    wcel
    #
    @3
    @20
    @6
    @0
    @23
    @22
    cG
    ngpgrp
    syl
    #
    @19
    cX
    cG
    cI
    cA
    ngpinvds.x
    ngpinvds.i
    grpinvcl
    syl2anc
    @6
    @23
    @4
    @21
    @24
    @18
    cX
    cG
    cI
    cB
    ngpinvds.x
    ngpinvds.i
    grpinvcl
    syl2anc
    @8
    @7
    cD
    cG
    @9
    @11
    cX
    @11
    eqid
    #
    ngpinvds.x
    @17
    ngpinvds.d
    ngpdsr
    syl3anc
    @6
    @0
    @3
    @4
    @16
    @14
    wceq
    @22
    @19
    @18
    cA
    cB
    cD
    cG
    @9
    @11
    cX
    @25
    ngpinvds.x
    @17
    ngpinvds.d
    ngpds
    syl3anc
    3eqtr4d
end
