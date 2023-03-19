include "wcel.mm"
include "coppc.mm"
include "cfv.mm"
include "cnx.mm"
include "chom.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cco.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "tposeqd.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "sqxpeqd.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "df-oppc.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem oppcval
  let vz: setvar z
  let vu: setvar u
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cH: class H
  let cO: class O
  let cV: class V
  let vc: setvar c
  assume oppcval.b: |- B = ( Base ` C )
  assume oppcval.h: |- H = ( Hom ` C )
  assume oppcval.x: |- .x. = ( comp ` C )
  assume oppcval.o: |- O = ( oppCat ` C )

  disjoint u z
  disjoint C u
  disjoint C z
  disjoint B c
  disjoint c u
  disjoint c z
  disjoint C c
  disjoint H c
  disjoint .x. c
  assert |- ( C e. V -> O = ( ( C sSet <. ( Hom ` ndx ) , tpos H >. ) sSet <. ( comp ` ndx ) , ( u e. ( B X. B ) , z e. B |-> tpos ( <. z , ( 2nd ` u ) >. .x. ( 1st ` u ) ) ) >. ) )

  proof
    cC
    cV
    wcel
    #
    cO
    cC
    coppc
    cfv
    #
    cC
    cnx
    chom
    cfv
    #
    cH
    ctpos
    #
    cop
    #
    csts
    co
    #
    cnx
    cco
    cfv
    #
    vu
    vz
    cB
    cB
    cxp
    #
    cB
    vz
    cv
    vu
    cv
    #
    c2nd
    cfv
    cop
    #
    @8
    c1st
    cfv
    #
    c.x
    co
    #
    ctpos
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    oppcval.o
    @0
    cC
    cvv
    wcel
    @1
    @15
    wceq
    cC
    cV
    elex
    vc
    cC
    vc
    cv
    #
    @2
    @16
    chom
    cfv
    #
    ctpos
    #
    cop
    #
    csts
    co
    #
    @6
    vu
    vz
    @16
    cbs
    cfv
    #
    @21
    cxp
    #
    @21
    @9
    @10
    @16
    cco
    cfv
    #
    co
    #
    ctpos
    #
    cmpt2
    #
    cop
    #
    csts
    co
    @15
    cvv
    coppc
    @16
    cC
    wceq
    #
    @20
    @5
    @27
    @14
    csts
    @28
    @16
    cC
    @19
    @4
    csts
    @28
    id
    @28
    @18
    @3
    @2
    @28
    @17
    cH
    @28
    @17
    cC
    chom
    cfv
    cH
    @16
    cC
    chom
    fveq2
    oppcval.h
    syl6eqr
    tposeqd
    opeq2d
    oveq12d
    @28
    @26
    @13
    @6
    @28
    vu
    vz
    @22
    @21
    @25
    @7
    cB
    @12
    @28
    @21
    cB
    @28
    @21
    cC
    cbs
    cfv
    cB
    @16
    cC
    cbs
    fveq2
    oppcval.b
    syl6eqr
    #
    sqxpeqd
    @29
    @28
    @24
    @11
    @28
    @23
    c.x
    @9
    @10
    @28
    @23
    cC
    cco
    cfv
    c.x
    @16
    cC
    cco
    fveq2
    oppcval.x
    syl6eqr
    oveqd
    tposeqd
    mpt2eq123dv
    opeq2d
    oveq12d
    vz
    vu
    vc
    df-oppc
    @5
    @14
    csts
    ovex
    fvmpt
    syl
    syl5eq
end
