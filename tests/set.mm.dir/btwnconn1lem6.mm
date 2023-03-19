include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wa.mm"
include "ccgr.mm"
include "simprrl.mm"
include "jca.mm"
include "simp11.mm"
include "simp21.mm"
include "simp23.mm"
include "cgrrflxd.mm"
include "simp33.mm"
include "adantr.mm"
include "simp31.mm"
include "simp22.mm"
include "simp2rr.mm"
include "ad2antrl.mm"
include "cgrcomand.mm"
include "simp2lr.mm"
include "cgrcomrand.mm"
include "3simpa.mm"
include "3anim3i.mm"
include "simpl.mm"
include "btwnconn1lem4.mm"
include "syl2an.mm"
include "cgrtr3and.mm"
include "cgrcomlrand.mm"
include "wi.mm"
include "cifs.mm"
include "brifs.mm"
include "ifscgr.mm"
include "sylbird.mm"
include "syl333anc.mm"
include "mp3and.mm"

theorem btwnconn1lem6
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\ ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\ ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) ) ) -> <. E , D >. Cgr <. E , d >. )

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
    vc
    cv
    #
    @1
    wcel
    #
    w3a
    #
    vd
    cv
    #
    @1
    wcel
    #
    vb
    cv
    #
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cA
    cB
    wne
    cB
    cC
    wne
    cC
    @7
    wne
    w3a
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    cB
    cA
    cD
    cop
    cbtwn
    wbr
    wa
    wa
    #
    cD
    cA
    @7
    cop
    cbtwn
    wbr
    #
    cD
    @7
    cop
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cC
    cA
    @10
    cop
    cbtwn
    wbr
    #
    cC
    @10
    cop
    #
    @19
    ccgr
    wbr
    #
    wa
    #
    wa
    @7
    cA
    @12
    cop
    #
    cbtwn
    wbr
    @7
    @12
    cop
    cC
    cB
    cop
    ccgr
    wbr
    wa
    @10
    @26
    cbtwn
    wbr
    @10
    @12
    cop
    cD
    cB
    cop
    ccgr
    wbr
    wa
    wa
    #
    w3a
    #
    cE
    cC
    @7
    cop
    #
    cbtwn
    wbr
    #
    cE
    cD
    @10
    cop
    cbtwn
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    @30
    @30
    wa
    #
    @29
    @29
    ccgr
    wbr
    #
    cE
    @7
    cop
    #
    @37
    ccgr
    wbr
    #
    wa
    #
    @19
    @23
    ccgr
    wbr
    #
    @7
    cD
    cop
    #
    @7
    @10
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cE
    cD
    cop
    cE
    @10
    cop
    ccgr
    wbr
    #
    @34
    @30
    @30
    @16
    @28
    @30
    @31
    simprrl
    #
    @46
    jca
    @16
    @39
    @33
    @16
    @36
    @38
    @16
    cC
    @7
    cN
    @0
    @2
    @3
    @9
    @15
    simp11
    #
    @4
    @5
    @6
    @8
    @15
    simp21
    #
    @4
    @5
    @6
    @8
    @15
    simp23
    #
    cgrrflxd
    @16
    cE
    @7
    cN
    @47
    @4
    @9
    @11
    @13
    @14
    simp33
    #
    @49
    cgrrflxd
    jca
    adantr
    @34
    @40
    @43
    @16
    @33
    cC
    @10
    cC
    cD
    cN
    @47
    @48
    @4
    @9
    @11
    @13
    @14
    simp31
    #
    @48
    @4
    @5
    @6
    @8
    @15
    simp22
    #
    @28
    @24
    @16
    @32
    @22
    @24
    @21
    @17
    @27
    simp2rr
    ad2antrl
    cgrcomand
    @16
    @33
    cD
    @7
    @10
    @7
    cN
    @47
    @52
    @49
    @51
    @49
    @16
    @33
    cD
    @7
    @10
    @7
    cD
    cC
    cN
    @47
    @52
    @49
    @51
    @49
    @52
    @48
    @16
    @33
    cD
    @7
    cC
    cD
    cN
    @47
    @52
    @49
    @48
    @52
    @28
    @20
    @16
    @32
    @18
    @20
    @25
    @17
    @27
    simp2lr
    ad2antrl
    cgrcomrand
    @16
    @4
    @9
    @11
    @13
    wa
    #
    w3a
    @28
    @10
    @7
    cop
    cD
    cC
    cop
    ccgr
    wbr
    @33
    @15
    @53
    @4
    @9
    @11
    @13
    @14
    3simpa
    3anim3i
    @28
    @32
    simpl
    cA
    cB
    cC
    cD
    cN
    vb
    vc
    vd
    btwnconn1lem4
    syl2an
    cgrtr3and
    cgrcomlrand
    jca
    @16
    @35
    @39
    @44
    w3a
    #
    @45
    wi
    #
    @33
    @16
    @0
    @5
    @14
    @8
    @6
    @5
    @14
    @8
    @11
    @55
    @47
    @48
    @50
    @49
    @52
    @48
    @50
    @49
    @51
    @0
    @5
    @14
    w3a
    @8
    @6
    @5
    w3a
    @14
    @8
    @11
    w3a
    w3a
    @54
    cC
    cE
    cop
    #
    @41
    cop
    @56
    @42
    cop
    cifs
    wbr
    @45
    cC
    cE
    @7
    cD
    cC
    cE
    @7
    @10
    cN
    brifs
    cC
    cE
    @7
    cD
    cC
    cE
    @7
    @10
    cN
    ifscgr
    sylbird
    syl333anc
    adantr
    mp3and
end
