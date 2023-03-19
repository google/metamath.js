include "wceq.mm"
include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "c0h.mm"
include "wcel.mm"
include "cin.mm"
include "csh.mm"
include "shsubcl.mm"
include "syl3anc.mm"
include "cva.mm"
include "chil.mm"
include "wb.mm"
include "shel.mm"
include "syl2anc.mm"
include "hvaddsub4.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "elind.mm"
include "eleqtrd.mm"
include "elch0.mm"
include "sylib.mm"
include "hvsubeq0.mm"
include "eqtr3d.mm"
include "eqcomd.mm"
include "jca.mm"

theorem shuni
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cH: class H
  let cK: class K
  assume shuni.1: |- ( ph -> H e. SH )
  assume shuni.2: |- ( ph -> K e. SH )
  assume shuni.3: |- ( ph -> ( H i^i K ) = 0H )
  assume shuni.4: |- ( ph -> A e. H )
  assume shuni.5: |- ( ph -> B e. K )
  assume shuni.6: |- ( ph -> C e. H )
  assume shuni.7: |- ( ph -> D e. K )
  assume shuni.8: |- ( ph -> ( A +h B ) = ( C +h D ) )


  assert |- ( ph -> ( A = C /\ B = D ) )

  proof
    wph
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    wph
    cA
    cC
    cmv
    co
    #
    c0v
    wceq
    #
    @0
    wph
    @1
    c0h
    wcel
    @2
    wph
    @1
    cH
    cK
    cin
    c0h
    wph
    cH
    cK
    @1
    wph
    cH
    csh
    wcel
    #
    cA
    cH
    wcel
    #
    cC
    cH
    wcel
    #
    @1
    cH
    wcel
    shuni.1
    shuni.4
    shuni.6
    cA
    cC
    cH
    shsubcl
    syl3anc
    wph
    @1
    cD
    cB
    cmv
    co
    #
    cK
    wph
    cA
    cB
    cva
    co
    cC
    cD
    cva
    co
    wceq
    #
    @1
    @6
    wceq
    #
    shuni.8
    wph
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    @7
    @8
    wb
    wph
    @3
    @4
    @9
    shuni.1
    shuni.4
    cA
    cH
    shel
    syl2anc
    #
    wph
    cK
    csh
    wcel
    #
    cB
    cK
    wcel
    #
    @10
    shuni.2
    shuni.5
    cB
    cK
    shel
    syl2anc
    #
    wph
    @3
    @5
    @11
    shuni.1
    shuni.6
    cC
    cH
    shel
    syl2anc
    #
    wph
    @14
    cD
    cK
    wcel
    #
    @12
    shuni.2
    shuni.7
    cD
    cK
    shel
    syl2anc
    #
    cA
    cB
    cC
    cD
    hvaddsub4
    syl22anc
    mpbid
    #
    wph
    @14
    @18
    @15
    @6
    cK
    wcel
    shuni.2
    shuni.7
    shuni.5
    cD
    cB
    cK
    shsubcl
    syl3anc
    eqeltrd
    elind
    shuni.3
    eleqtrd
    @1
    elch0
    sylib
    #
    wph
    @9
    @11
    @2
    @0
    wb
    @13
    @17
    cA
    cC
    hvsubeq0
    syl2anc
    mpbid
    wph
    cD
    cB
    wph
    @6
    c0v
    wceq
    #
    cD
    cB
    wceq
    #
    wph
    @1
    @6
    c0v
    @20
    @21
    eqtr3d
    wph
    @12
    @10
    @22
    @23
    wb
    @19
    @16
    cD
    cB
    hvsubeq0
    syl2anc
    mpbid
    eqcomd
    jca
end
