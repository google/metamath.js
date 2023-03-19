include "cop.mm"
include "cec.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "brel.mm"
include "cxp.mm"
include "cqs.mm"
include "cdm.mm"
include "wceq.mm"
include "ecelqsdm.mm"
include "mpan.mm"
include "eleq2s.mm"
include "opelxp.mm"
include "sylib.mm"
include "anim12i.mm"
include "syl.mm"
include "ndmovrcl.mm"
include "an42.mm"
include "pm5.21nii.mm"

theorem brecop2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cR: class R
  let cG: class G
  let cH: class H
  let c.le: class .<_
  assume brecop2.1: |- .~ e. _V
  assume brecop2.5: |- dom .~ = ( G X. G )
  assume brecop2.6: |- H = ( ( G X. G ) /. .~ )
  assume brecop2.7: |- R C_ ( H X. H )
  assume brecop2.8: |- .<_ C_ ( G X. G )
  assume brecop2.9: |- -. (/) e. G
  assume brecop2.10: |- dom .+ = ( G X. G )
  assume brecop2.11: |- ( ( ( A e. G /\ B e. G ) /\ ( C e. G /\ D e. G ) ) -> ( [ <. A , B >. ] .~ R [ <. C , D >. ] .~ <-> ( A .+ D ) .<_ ( B .+ C ) ) )


  assert |- ( [ <. A , B >. ] .~ R [ <. C , D >. ] .~ <-> ( A .+ D ) .<_ ( B .+ C ) )

  proof
    cA
    cB
    cop
    #
    c.sm
    cec
    #
    cC
    cD
    cop
    #
    c.sm
    cec
    #
    cR
    wbr
    #
    cA
    cG
    wcel
    #
    cB
    cG
    wcel
    #
    wa
    #
    cC
    cG
    wcel
    #
    cD
    cG
    wcel
    #
    wa
    #
    wa
    #
    cA
    cD
    c.pl
    co
    #
    cB
    cC
    c.pl
    co
    #
    c.le
    wbr
    #
    @4
    @1
    cH
    wcel
    #
    @3
    cH
    wcel
    #
    wa
    @11
    @1
    @3
    cH
    cH
    cR
    brecop2.7
    brel
    @15
    @7
    @16
    @10
    @15
    @0
    cG
    cG
    cxp
    #
    wcel
    #
    @7
    @18
    @1
    @17
    c.sm
    cqs
    #
    cH
    c.sm
    cdm
    @17
    wceq
    #
    @1
    @19
    wcel
    @18
    brecop2.5
    @17
    @0
    c.sm
    ecelqsdm
    mpan
    brecop2.6
    eleq2s
    cA
    cB
    cG
    cG
    opelxp
    sylib
    @16
    @2
    @17
    wcel
    #
    @10
    @21
    @3
    @19
    cH
    @20
    @3
    @19
    wcel
    @21
    brecop2.5
    @17
    @2
    c.sm
    ecelqsdm
    mpan
    brecop2.6
    eleq2s
    cC
    cD
    cG
    cG
    opelxp
    sylib
    anim12i
    syl
    @14
    @5
    @9
    wa
    #
    @6
    @8
    wa
    #
    wa
    #
    @11
    @14
    @12
    cG
    wcel
    #
    @13
    cG
    wcel
    #
    wa
    @24
    @12
    @13
    cG
    cG
    c.le
    brecop2.8
    brel
    @25
    @22
    @26
    @23
    cA
    cD
    cG
    c.pl
    brecop2.10
    brecop2.9
    ndmovrcl
    cB
    cC
    cG
    c.pl
    brecop2.10
    brecop2.9
    ndmovrcl
    anim12i
    syl
    @5
    @9
    @6
    @8
    an42
    sylib
    brecop2.11
    pm5.21nii
end
