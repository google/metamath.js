include "ccyg.mm"
include "wcel.mm"
include "wa.mm"
include "cgic.mm"
include "wbr.mm"
include "cen.mm"
include "gicen.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cif.mm"
include "czn.mm"
include "eqid.mm"
include "cygzn.mm"
include "ad2antrr.mm"
include "wb.mm"
include "enfi.mm"
include "adantl.mm"
include "wceq.mm"
include "hasheni.mm"
include "ifbieq1d.mm"
include "fveq2d.mm"
include "ad2antlr.mm"
include "gicsym.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "gictr.mm"
include "syl2anc.mm"
include "ex.mm"
include "impbid2.mm"

theorem cyggic
  let cB: class B
  let cC: class C
  let cG: class G
  let cH: class H
  assume cygctb.b: |- B = ( Base ` G )
  assume cygctb.c: |- C = ( Base ` H )


  assert |- ( ( G e. CycGrp /\ H e. CycGrp ) -> ( G ~=g H <-> B ~~ C ) )

  proof
    cG
    ccyg
    wcel
    #
    cH
    ccyg
    wcel
    #
    wa
    #
    cG
    cH
    cgic
    wbr
    #
    cB
    cC
    cen
    wbr
    #
    cB
    cC
    cG
    cH
    cygctb.b
    cygctb.c
    gicen
    @2
    @4
    @3
    @2
    @4
    wa
    #
    cG
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cif
    #
    czn
    cfv
    #
    cgic
    wbr
    #
    @9
    cH
    cgic
    wbr
    @3
    @0
    @10
    @1
    @4
    cB
    cG
    @8
    @9
    cygctb.b
    @8
    eqid
    @9
    eqid
    cygzn
    ad2antrr
    @5
    @9
    cC
    cfn
    wcel
    #
    cC
    chash
    cfv
    #
    cc0
    cif
    #
    czn
    cfv
    #
    cH
    cgic
    @5
    @8
    @13
    czn
    @5
    @6
    @11
    @7
    @12
    cc0
    @4
    @6
    @11
    wb
    @2
    cB
    cC
    enfi
    adantl
    @4
    @7
    @12
    wceq
    @2
    cB
    cC
    hasheni
    adantl
    ifbieq1d
    fveq2d
    @5
    cH
    @14
    cgic
    wbr
    #
    @14
    cH
    cgic
    wbr
    @1
    @15
    @0
    @4
    cC
    cH
    @13
    @14
    cygctb.c
    @13
    eqid
    @14
    eqid
    cygzn
    ad2antlr
    cH
    @14
    gicsym
    syl
    eqbrtrd
    cG
    @9
    cH
    gictr
    syl2anc
    ex
    impbid2
end
