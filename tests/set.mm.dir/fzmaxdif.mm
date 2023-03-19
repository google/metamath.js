include "cz.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "simp2r.mm"
include "elfzelz.mm"
include "syl.mm"
include "zred.mm"
include "simp2l.mm"
include "simp1r.mm"
include "elfzel1.mm"
include "resubcld.mm"
include "elfzle2.mm"
include "lesub1dd.mm"
include "recnd.mm"
include "nncand.mm"
include "breqtrd.mm"
include "elfzle1.mm"
include "letrd.mm"
include "simp1l.mm"
include "readdcld.mm"
include "lesub2dd.mm"
include "simp3.mm"
include "lesubaddd.mm"
include "mpbid.mm"
include "addcomd.mm"
include "absdifled.mm"
include "mpbir2and.mm"

theorem fzmaxdif
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- ( ( ( C e. ZZ /\ A e. ( B ... C ) ) /\ ( F e. ZZ /\ D e. ( E ... F ) ) /\ ( C - E ) <_ ( F - B ) ) -> ( abs ` ( A - D ) ) <_ ( F - B ) )

  proof
    cC
    cz
    wcel
    #
    cA
    cB
    cC
    cfz
    co
    wcel
    #
    wa
    #
    cF
    cz
    wcel
    #
    cD
    cE
    cF
    cfz
    co
    wcel
    #
    wa
    #
    cC
    cE
    cmin
    co
    #
    cF
    cB
    cmin
    co
    #
    cle
    wbr
    #
    w3a
    #
    cA
    cD
    cmin
    co
    cabs
    cfv
    @7
    cle
    wbr
    cD
    @7
    cmin
    co
    #
    cA
    cle
    wbr
    cA
    cD
    @7
    caddc
    co
    #
    cle
    wbr
    @9
    @10
    cB
    cA
    @9
    cD
    @7
    @9
    cD
    @9
    @4
    cD
    cz
    wcel
    @2
    @3
    @4
    @8
    simp2r
    #
    cD
    cE
    cF
    elfzelz
    syl
    zred
    #
    @9
    cF
    cB
    @9
    cF
    @2
    @3
    @4
    @8
    simp2l
    zred
    #
    @9
    cB
    @9
    @1
    cB
    cz
    wcel
    @0
    @1
    @5
    @8
    simp1r
    #
    cA
    cB
    cC
    elfzel1
    syl
    zred
    #
    resubcld
    #
    resubcld
    @16
    @9
    cA
    @9
    @1
    cA
    cz
    wcel
    @15
    cA
    cB
    cC
    elfzelz
    syl
    zred
    #
    @9
    @10
    cF
    @7
    cmin
    co
    cB
    cle
    @9
    cD
    cF
    @7
    @13
    @14
    @17
    @9
    @4
    cD
    cF
    cle
    wbr
    @12
    cD
    cE
    cF
    elfzle2
    syl
    lesub1dd
    @9
    cF
    cB
    @9
    cF
    @14
    recnd
    @9
    cB
    @16
    recnd
    nncand
    breqtrd
    @9
    @1
    cB
    cA
    cle
    wbr
    @15
    cA
    cB
    cC
    elfzle1
    syl
    letrd
    @9
    cA
    cC
    @11
    @18
    @9
    cC
    @0
    @1
    @5
    @8
    simp1l
    zred
    #
    @9
    cD
    @7
    @13
    @17
    readdcld
    @9
    @1
    cA
    cC
    cle
    wbr
    @15
    cA
    cB
    cC
    elfzle2
    syl
    @9
    cC
    @7
    cD
    caddc
    co
    #
    @11
    cle
    @9
    cC
    cD
    cmin
    co
    #
    @7
    cle
    wbr
    cC
    @20
    cle
    wbr
    @9
    @21
    @6
    @7
    @9
    cC
    cD
    @19
    @13
    resubcld
    @9
    cC
    cE
    @19
    @9
    cE
    @9
    @4
    cE
    cz
    wcel
    @12
    cD
    cE
    cF
    elfzel1
    syl
    zred
    #
    resubcld
    @17
    @9
    cE
    cD
    cC
    @22
    @13
    @19
    @9
    @4
    cE
    cD
    cle
    wbr
    @12
    cD
    cE
    cF
    elfzle1
    syl
    lesub2dd
    @2
    @5
    @8
    simp3
    letrd
    @9
    cC
    cD
    @7
    @19
    @13
    @17
    lesubaddd
    mpbid
    @9
    @7
    cD
    @9
    @7
    @17
    recnd
    @9
    cD
    @13
    recnd
    addcomd
    breqtrd
    letrd
    @9
    cA
    cD
    @7
    @18
    @13
    @17
    absdifled
    mpbir2and
end
