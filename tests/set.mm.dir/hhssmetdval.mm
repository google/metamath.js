include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cmv.mm"
include "cxp.mm"
include "cres.mm"
include "cno.mm"
include "cfv.mm"
include "cnv.mm"
include "wceq.mm"
include "hhssnv.mm"
include "hhssba.mm"
include "hhssvs.mm"
include "hhssnm.mm"
include "imsdval.mm"
include "mp3an1.mm"
include "ovres.mm"
include "fveq2d.mm"
include "csh.mm"
include "shsubcl.mm"
include "fvres.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem hhssmetdval
  let cA: class A
  let cB: class B
  let cD: class D
  let cH: class H
  let cW: class W
  assume hhssims2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssims2.3: |- D = ( IndMet ` W )
  assume hhssims2.2: |- H e. SH


  assert |- ( ( A e. H /\ B e. H ) -> ( A D B ) = ( normh ` ( A -h B ) ) )

  proof
    cA
    cH
    wcel
    #
    cB
    cH
    wcel
    #
    wa
    #
    cA
    cB
    cD
    co
    #
    cA
    cB
    cmv
    cH
    cH
    cxp
    cres
    #
    co
    #
    cno
    cH
    cres
    #
    cfv
    #
    cA
    cB
    cmv
    co
    #
    @6
    cfv
    #
    @8
    cno
    cfv
    #
    cW
    cnv
    wcel
    @0
    @1
    @3
    @7
    wceq
    cH
    cW
    hhssims2.1
    hhssims2.2
    hhssnv
    cA
    cB
    cD
    cW
    @4
    @6
    cH
    cH
    cW
    hhssims2.1
    hhssims2.2
    hhssba
    cH
    cW
    hhssims2.1
    hhssims2.2
    hhssvs
    cH
    cW
    hhssims2.1
    hhssnm
    hhssims2.3
    imsdval
    mp3an1
    @2
    @5
    @8
    @6
    cA
    cB
    cH
    cH
    cmv
    ovres
    fveq2d
    @2
    @8
    cH
    wcel
    #
    @9
    @10
    wceq
    cH
    csh
    wcel
    @0
    @1
    @11
    hhssims2.2
    cA
    cB
    cH
    shsubcl
    mp3an1
    @8
    cH
    cno
    fvres
    syl
    3eqtrd
end
