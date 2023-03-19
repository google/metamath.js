include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "ccom.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "cmt.mm"
include "eqid.mm"
include "isngp2.mm"
include "simp3bi.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "cop.mm"
include "wf.mm"
include "ngpgrp.mm"
include "grpsubf.mm"
include "syl.mm"
include "opelxpi.mm"
include "3adant1.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "ovres.mm"
include "3eqtr3rd.mm"

theorem ngpds
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume ngpds.n: |- N = ( norm ` G )
  assume ngpds.x: |- X = ( Base ` G )
  assume ngpds.m: |- .- = ( -g ` G )
  assume ngpds.d: |- D = ( dist ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( A D B ) = ( N ` ( A .- B ) ) )

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
    cN
    c.mi
    ccom
    #
    co
    #
    cA
    cB
    cD
    cX
    cX
    cxp
    #
    cres
    #
    co
    #
    cA
    cB
    c.mi
    co
    #
    cN
    cfv
    #
    cA
    cB
    cD
    co
    #
    @3
    @4
    @7
    cA
    cB
    @0
    @1
    @4
    @7
    wceq
    #
    @2
    @0
    cG
    cgrp
    wcel
    #
    cG
    cmt
    wcel
    @12
    cD
    @7
    cG
    c.mi
    cN
    cX
    ngpds.n
    ngpds.m
    ngpds.d
    ngpds.x
    @7
    eqid
    isngp2
    simp3bi
    3ad2ant1
    oveqd
    @3
    cA
    cB
    cop
    #
    @4
    cfv
    #
    @14
    c.mi
    cfv
    #
    cN
    cfv
    #
    @5
    @10
    @3
    @6
    cX
    c.mi
    wf
    #
    @14
    @6
    wcel
    #
    @15
    @17
    wceq
    @0
    @1
    @18
    @2
    @0
    @13
    @18
    cG
    ngpgrp
    cX
    cG
    c.mi
    ngpds.x
    ngpds.m
    grpsubf
    syl
    3ad2ant1
    @1
    @2
    @19
    @0
    cA
    cB
    cX
    cX
    opelxpi
    3adant1
    @6
    cX
    @14
    cN
    c.mi
    fvco3
    syl2anc
    cA
    cB
    @4
    df-ov
    @9
    @16
    cN
    cA
    cB
    c.mi
    df-ov
    fveq2i
    3eqtr4g
    @1
    @2
    @8
    @11
    wceq
    @0
    cA
    cB
    cX
    cX
    cD
    ovres
    3adant1
    3eqtr3rd
end
