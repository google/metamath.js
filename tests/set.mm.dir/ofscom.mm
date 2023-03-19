include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wa.mm"
include "ccgr.mm"
include "cofs.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp23.mm"
include "simp31.mm"
include "cgrcom.mm"
include "syl122anc.mm"
include "simp21.mm"
include "simp32.mm"
include "anbi12d.mm"
include "simp22.mm"
include "simp33.mm"
include "3anbi123d.mm"
include "brofs.mm"
include "syl333anc.mm"
include "3bitr4d.mm"

theorem ofscom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\ ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) -> ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg <. <. E , F >. , <. G , H >. >. <-> <. <. E , F >. , <. G , H >. >. OuterFiveSeg <. <. A , B >. , <. C , D >. >. ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    w3a
    #
    cF
    @1
    wcel
    #
    cG
    @1
    wcel
    #
    cH
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cF
    cE
    cG
    cop
    cbtwn
    wbr
    #
    wa
    #
    cA
    cB
    cop
    #
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    cB
    cC
    cop
    #
    cF
    cG
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cA
    cD
    cop
    #
    cE
    cH
    cop
    #
    ccgr
    wbr
    #
    cB
    cD
    cop
    #
    cF
    cH
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    w3a
    @15
    @14
    wa
    #
    @18
    @17
    ccgr
    wbr
    #
    @21
    @20
    ccgr
    wbr
    #
    wa
    #
    @25
    @24
    ccgr
    wbr
    #
    @28
    @27
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    @17
    cC
    cD
    cop
    cop
    #
    @18
    cG
    cH
    cop
    cop
    #
    cofs
    wbr
    @40
    @39
    cofs
    wbr
    #
    @13
    @16
    @31
    @23
    @34
    @30
    @37
    @16
    @31
    wb
    @13
    @14
    @15
    ancom
    a1i
    @13
    @19
    @32
    @22
    @33
    @13
    @0
    @2
    @3
    @7
    @9
    @19
    @32
    wb
    @0
    @2
    @3
    @8
    @12
    simp11
    #
    @0
    @2
    @3
    @8
    @12
    simp12
    #
    @0
    @2
    @3
    @8
    @12
    simp13
    #
    @4
    @5
    @6
    @7
    @12
    simp23
    #
    @4
    @8
    @9
    @10
    @11
    simp31
    #
    cA
    cB
    cE
    cF
    cN
    cgrcom
    syl122anc
    @13
    @0
    @3
    @5
    @9
    @10
    @22
    @33
    wb
    @42
    @44
    @4
    @5
    @6
    @7
    @12
    simp21
    #
    @46
    @4
    @8
    @9
    @10
    @11
    simp32
    #
    cB
    cC
    cF
    cG
    cN
    cgrcom
    syl122anc
    anbi12d
    @13
    @26
    @35
    @29
    @36
    @13
    @0
    @2
    @6
    @7
    @11
    @26
    @35
    wb
    @42
    @43
    @4
    @5
    @6
    @7
    @12
    simp22
    #
    @45
    @4
    @8
    @9
    @10
    @11
    simp33
    #
    cA
    cD
    cE
    cH
    cN
    cgrcom
    syl122anc
    @13
    @0
    @3
    @6
    @9
    @11
    @29
    @36
    wb
    @42
    @44
    @49
    @46
    @50
    cB
    cD
    cF
    cH
    cN
    cgrcom
    syl122anc
    anbi12d
    3anbi123d
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cN
    brofs
    @13
    @0
    @7
    @9
    @10
    @11
    @2
    @3
    @5
    @6
    @41
    @38
    wb
    @42
    @45
    @46
    @48
    @50
    @43
    @44
    @47
    @49
    cE
    cF
    cG
    cH
    cA
    cB
    cC
    cD
    cN
    brofs
    syl333anc
    3bitr4d
end
