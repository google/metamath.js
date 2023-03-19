include "wcel.mm"
include "wa.mm"
include "cresc.mm"
include "co.mm"
include "cdm.mm"
include "cress.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "simpl.mm"
include "simpr.mm"
include "dmeqd.mm"
include "oveq12d.mm"
include "opeq2d.mm"
include "df-resc.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem rescval
  let cC: class C
  let cD: class D
  let cH: class H
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vh: setvar h
  assume rescval.1: |- D = ( C |`cat H )


  assert |- ( ( C e. V /\ H e. W ) -> D = ( ( C |`s dom dom H ) sSet <. ( Hom ` ndx ) , H >. ) )

  proof
    cC
    cV
    wcel
    #
    cH
    cW
    wcel
    #
    wa
    cD
    cC
    cH
    cresc
    co
    #
    cC
    cH
    cdm
    #
    cdm
    #
    cress
    co
    #
    cnx
    chom
    cfv
    #
    cH
    cop
    #
    csts
    co
    #
    rescval.1
    @0
    cC
    cvv
    wcel
    cH
    cvv
    wcel
    @2
    @8
    wceq
    @1
    cC
    cV
    elex
    cH
    cW
    elex
    vc
    vh
    cC
    cH
    cvv
    cvv
    vc
    cv
    #
    vh
    cv
    #
    cdm
    #
    cdm
    #
    cress
    co
    #
    @6
    @10
    cop
    #
    csts
    co
    @8
    cresc
    @9
    cC
    wceq
    #
    @10
    cH
    wceq
    #
    wa
    #
    @13
    @5
    @14
    @7
    csts
    @17
    @9
    cC
    @12
    @4
    cress
    @15
    @16
    simpl
    @17
    @11
    @3
    @17
    @10
    cH
    @15
    @16
    simpr
    #
    dmeqd
    dmeqd
    oveq12d
    @17
    @10
    cH
    @6
    @18
    opeq2d
    oveq12d
    vh
    vc
    df-resc
    @5
    @7
    csts
    ovex
    ovmpt2a
    syl2an
    syl5eq
end
