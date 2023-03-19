include "wor.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "cif.mm"
include "wpo.mm"
include "cid.mm"
include "cun.mm"
include "sopo.mm"
include "ad2antrr.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simplr3.mm"
include "ifcld.mm"
include "3jca.mm"
include "simpr.mm"
include "simpll.mm"
include "somin1.mm"
include "syl12anc.mm"
include "poltletr.mm"
include "imp.mm"
include "syl22anc.mm"
include "somin2.mm"
include "jca.mm"
include "ex.mm"
include "breq2.mm"
include "ifboth.mm"
include "impbid1.mm"

theorem soltmin
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X


  assert |- ( ( R Or X /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A R if ( B R C , B , C ) <-> ( A R B /\ A R C ) ) )

  proof
    cX
    cR
    wor
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cR
    wbr
    #
    cB
    cC
    cif
    #
    cR
    wbr
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cC
    cR
    wbr
    #
    wa
    #
    @5
    @8
    @11
    @5
    @8
    wa
    #
    @9
    @10
    @12
    cX
    cR
    wpo
    #
    @1
    @7
    cX
    wcel
    #
    @2
    w3a
    #
    @8
    @7
    cB
    cR
    cid
    cun
    #
    wbr
    #
    @9
    @0
    @13
    @4
    @8
    cX
    cR
    sopo
    ad2antrr
    #
    @12
    @1
    @14
    @2
    @1
    @2
    @3
    @0
    @8
    simplr1
    #
    @12
    @6
    cB
    cC
    cX
    @1
    @2
    @3
    @0
    @8
    simplr2
    #
    @1
    @2
    @3
    @0
    @8
    simplr3
    #
    ifcld
    #
    @20
    3jca
    @5
    @8
    simpr
    #
    @12
    @0
    @2
    @3
    @17
    @0
    @4
    @8
    simpll
    #
    @20
    @21
    cB
    cC
    cR
    cX
    somin1
    syl12anc
    @13
    @15
    wa
    @8
    @17
    wa
    @9
    cA
    @7
    cB
    cR
    cX
    poltletr
    imp
    syl22anc
    @12
    @13
    @1
    @14
    @3
    w3a
    #
    @8
    @7
    cC
    @16
    wbr
    #
    @10
    @18
    @12
    @1
    @14
    @3
    @19
    @22
    @21
    3jca
    @23
    @12
    @0
    @2
    @3
    @26
    @24
    @20
    @21
    cB
    cC
    cR
    cX
    somin2
    syl12anc
    @13
    @25
    wa
    @8
    @26
    wa
    @10
    cA
    @7
    cC
    cR
    cX
    poltletr
    imp
    syl22anc
    jca
    ex
    @6
    @9
    @10
    @8
    cB
    cC
    cB
    @7
    cA
    cR
    breq2
    cC
    @7
    cA
    cR
    breq2
    ifboth
    impbid1
end
