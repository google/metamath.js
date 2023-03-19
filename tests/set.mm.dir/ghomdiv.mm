include "cgr.mm"
include "wcel.mm"
include "cghomOLD.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "simpl2.mm"
include "eqid.mm"
include "ghomf.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "grponpcan.mm"
include "syl3anc.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "fveq2d.mm"
include "grpodivcl.mm"
include "simprr.mm"
include "jca.mm"
include "ghomlinOLD.mm"
include "eqcomd.mm"
include "syldan.mm"
include "3eqtr2rd.mm"
include "wb.mm"
include "grporcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem ghomdiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  assume ghomdiv.1: |- X = ran G
  assume ghomdiv.2: |- D = ( /g ` G )
  assume ghomdiv.3: |- C = ( /g ` H )


  assert |- ( ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) /\ ( A e. X /\ B e. X ) ) -> ( F ` ( A D B ) ) = ( ( F ` A ) C ( F ` B ) ) )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cF
    cG
    cH
    cghomOLD
    co
    wcel
    #
    w3a
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
    cA
    cB
    cD
    co
    #
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cH
    co
    #
    cA
    cF
    cfv
    #
    @10
    cC
    co
    #
    @10
    cH
    co
    #
    wceq
    #
    @9
    @13
    wceq
    #
    @7
    @14
    @12
    @8
    cB
    cG
    co
    #
    cF
    cfv
    #
    @11
    @7
    @1
    @12
    cH
    crn
    #
    wcel
    #
    @10
    @19
    wcel
    #
    @14
    @12
    wceq
    @0
    @1
    @2
    @6
    simpl2
    #
    @3
    @4
    @20
    @5
    @3
    cX
    @19
    cA
    cF
    cF
    cG
    cH
    @19
    cX
    ghomdiv.1
    @19
    eqid
    #
    ghomf
    #
    ffvelrnda
    adantrr
    #
    @3
    @5
    @21
    @4
    @3
    cX
    @19
    cB
    cF
    @24
    ffvelrnda
    adantrl
    #
    @12
    @10
    cC
    cH
    @19
    @23
    ghomdiv.3
    grponpcan
    syl3anc
    @7
    @17
    cA
    cF
    @0
    @1
    @6
    @17
    cA
    wceq
    #
    @2
    @0
    @4
    @5
    @27
    cA
    cB
    cD
    cG
    cX
    ghomdiv.1
    ghomdiv.2
    grponpcan
    3expb
    3ad2antl1
    fveq2d
    @3
    @6
    @8
    cX
    wcel
    #
    @5
    wa
    #
    @18
    @11
    wceq
    @0
    @1
    @6
    @29
    @2
    @0
    @6
    wa
    @28
    @5
    @0
    @4
    @5
    @28
    cA
    cB
    cD
    cG
    cX
    ghomdiv.1
    ghomdiv.2
    grpodivcl
    3expb
    #
    @0
    @4
    @5
    simprr
    jca
    3ad2antl1
    @3
    @29
    wa
    @11
    @18
    @8
    cB
    cF
    cG
    cH
    cX
    ghomdiv.1
    ghomlinOLD
    eqcomd
    syldan
    3eqtr2rd
    @7
    @1
    @9
    @19
    wcel
    #
    @13
    @19
    wcel
    #
    @21
    @15
    @16
    wb
    @22
    @3
    @6
    @28
    @31
    @0
    @1
    @6
    @28
    @2
    @30
    3ad2antl1
    @3
    cX
    @19
    @8
    cF
    @24
    ffvelrnda
    syldan
    @7
    @1
    @20
    @21
    @32
    @22
    @25
    @26
    @12
    @10
    cC
    cH
    @19
    @23
    ghomdiv.3
    grpodivcl
    syl3anc
    @26
    @9
    @13
    @10
    cH
    @19
    @23
    grporcan
    syl13anc
    mpbid
end
