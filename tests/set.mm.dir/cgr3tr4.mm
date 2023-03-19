include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "ccgr3.mm"
include "3an6.mm"
include "wi.mm"
include "simpl.mm"
include "simpr11.mm"
include "simpr12.mm"
include "simpr21.mm"
include "simpr22.mm"
include "simpr31.mm"
include "simpr32.mm"
include "axcgrtr.mm"
include "syl133anc.mm"
include "simpr13.mm"
include "simpr23.mm"
include "simpr33.mm"
include "3anim123d.mm"
include "syl5bir.mm"
include "wb.mm"
include "brcgr3.mm"
include "3adant3r3.mm"
include "3adant3r2.mm"
include "anbi12d.mm"
include "3adant3r1.mm"
include "3imtr4d.mm"

theorem cgr3tr4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N


  assert |- ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) /\ ( G e. ( EE ` N ) /\ H e. ( EE ` N ) /\ I e. ( EE ` N ) ) ) ) -> ( ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. /\ <. A , <. B , C >. >. Cgr3 <. G , <. H , I >. >. ) -> <. D , <. E , F >. >. Cgr3 <. G , <. H , I >. >. ) )

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
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    w3a
    #
    cG
    @1
    wcel
    #
    cH
    @1
    wcel
    #
    cI
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    wa
    #
    cA
    cB
    cop
    #
    cD
    cE
    cop
    #
    ccgr
    wbr
    #
    cA
    cC
    cop
    #
    cD
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
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    w3a
    #
    @16
    cG
    cH
    cop
    #
    ccgr
    wbr
    #
    @19
    cG
    cI
    cop
    #
    ccgr
    wbr
    #
    @22
    cH
    cI
    cop
    #
    ccgr
    wbr
    #
    w3a
    #
    wa
    #
    @17
    @26
    ccgr
    wbr
    #
    @20
    @28
    ccgr
    wbr
    #
    @23
    @30
    ccgr
    wbr
    #
    w3a
    #
    cA
    @22
    cop
    #
    cD
    @23
    cop
    #
    ccgr3
    wbr
    #
    @38
    cG
    @30
    cop
    #
    ccgr3
    wbr
    #
    wa
    @39
    @41
    ccgr3
    wbr
    #
    @33
    @18
    @27
    wa
    #
    @21
    @29
    wa
    #
    @24
    @31
    wa
    #
    w3a
    @15
    @37
    @18
    @27
    @21
    @29
    @24
    @31
    3an6
    @15
    @44
    @34
    @45
    @35
    @46
    @36
    @15
    @0
    @2
    @3
    @6
    @7
    @10
    @11
    @44
    @34
    wi
    @0
    @14
    simpl
    #
    @2
    @3
    @4
    @9
    @13
    @0
    simpr11
    #
    @2
    @3
    @4
    @9
    @13
    @0
    simpr12
    #
    @6
    @7
    @8
    @5
    @13
    @0
    simpr21
    #
    @6
    @7
    @8
    @5
    @13
    @0
    simpr22
    #
    @10
    @11
    @12
    @5
    @9
    @0
    simpr31
    #
    @10
    @11
    @12
    @5
    @9
    @0
    simpr32
    #
    cA
    cB
    cD
    cE
    cG
    cH
    cN
    axcgrtr
    syl133anc
    @15
    @0
    @2
    @4
    @6
    @8
    @10
    @12
    @45
    @35
    wi
    @47
    @48
    @2
    @3
    @4
    @9
    @13
    @0
    simpr13
    #
    @50
    @6
    @7
    @8
    @5
    @13
    @0
    simpr23
    #
    @52
    @10
    @11
    @12
    @5
    @9
    @0
    simpr33
    #
    cA
    cC
    cD
    cF
    cG
    cI
    cN
    axcgrtr
    syl133anc
    @15
    @0
    @3
    @4
    @7
    @8
    @11
    @12
    @46
    @36
    wi
    @47
    @49
    @54
    @51
    @55
    @53
    @56
    cB
    cC
    cE
    cF
    cH
    cI
    cN
    axcgrtr
    syl133anc
    3anim123d
    syl5bir
    @15
    @40
    @25
    @42
    @32
    @0
    @5
    @9
    @40
    @25
    wb
    @13
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    brcgr3
    3adant3r3
    @0
    @5
    @13
    @42
    @32
    wb
    @9
    cA
    cB
    cC
    cG
    cH
    cI
    cN
    brcgr3
    3adant3r2
    anbi12d
    @0
    @9
    @13
    @43
    @37
    wb
    @5
    cD
    cE
    cF
    cG
    cH
    cI
    cN
    brcgr3
    3adant3r1
    3imtr4d
end
