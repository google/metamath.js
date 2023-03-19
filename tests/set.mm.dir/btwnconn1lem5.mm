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
include "ccgr3.mm"
include "simprrr.mm"
include "simp11.mm"
include "simp22.mm"
include "simp33.mm"
include "simp31.mm"
include "cgr3rflx.mm"
include "syl13anc.mm"
include "adantr.mm"
include "simp2lr.mm"
include "ad2antrl.mm"
include "wb.mm"
include "simp23.mm"
include "simp21.mm"
include "cgrcomr.mm"
include "syl122anc.mm"
include "cgrcom.mm"
include "bitrd.mm"
include "mpbid.mm"
include "simp2rr.mm"
include "cgrcomlrand.mm"
include "3simpa.mm"
include "3anim3i.mm"
include "simpl.mm"
include "btwnconn1lem4.mm"
include "syl2an.mm"
include "cgrtr3and.mm"
include "jca.mm"
include "wi.mm"
include "cifs.mm"
include "brifs2.mm"
include "ifscgr.mm"
include "sylbird.mm"
include "syl333anc.mm"
include "mp3and.mm"

theorem btwnconn1lem5
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\ ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\ ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) ) ) -> <. E , C >. Cgr <. E , c >. )

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
    #
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
    @20
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
    cD
    cE
    @10
    cop
    cop
    #
    @34
    ccgr3
    wbr
    #
    cD
    cC
    cop
    #
    @19
    ccgr
    wbr
    #
    @10
    cC
    cop
    #
    @10
    @7
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cE
    cC
    cop
    cE
    @7
    cop
    ccgr
    wbr
    #
    @16
    @28
    @29
    @30
    simprrr
    @16
    @35
    @32
    @16
    @0
    @6
    @14
    @11
    @35
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
    simp22
    #
    @4
    @9
    @11
    @13
    @14
    simp33
    #
    @4
    @9
    @11
    @13
    @14
    simp31
    #
    cD
    cE
    @10
    cN
    cgr3rflx
    syl13anc
    adantr
    @33
    @37
    @40
    @33
    @21
    @37
    @28
    @21
    @16
    @31
    @18
    @21
    @25
    @17
    @27
    simp2lr
    ad2antrl
    @16
    @21
    @37
    wb
    @32
    @16
    @21
    @19
    @36
    ccgr
    wbr
    #
    @37
    @16
    @0
    @6
    @8
    @5
    @6
    @21
    @47
    wb
    @43
    @44
    @4
    @5
    @6
    @8
    @15
    simp23
    #
    @4
    @5
    @6
    @8
    @15
    simp21
    #
    @44
    cD
    @7
    cC
    cD
    cN
    cgrcomr
    syl122anc
    @16
    @0
    @6
    @8
    @6
    @5
    @47
    @37
    wb
    @43
    @44
    @48
    @44
    @49
    cD
    @7
    cD
    cC
    cN
    cgrcom
    syl122anc
    bitrd
    adantr
    mpbid
    @16
    @32
    @10
    cC
    @10
    @7
    cD
    cC
    cN
    @43
    @46
    @49
    @46
    @48
    @44
    @49
    @16
    @32
    cC
    @10
    cC
    cD
    cN
    @43
    @49
    @46
    @49
    @44
    @28
    @24
    @16
    @31
    @23
    @24
    @22
    @17
    @27
    simp2rr
    ad2antrl
    cgrcomlrand
    @16
    @4
    @9
    @11
    @13
    wa
    #
    w3a
    @28
    @39
    @36
    ccgr
    wbr
    @32
    @15
    @50
    @4
    @9
    @11
    @13
    @14
    3simpa
    3anim3i
    @28
    @31
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
    jca
    @16
    @30
    @35
    @41
    w3a
    #
    @42
    wi
    #
    @32
    @16
    @0
    @6
    @14
    @11
    @5
    @6
    @14
    @11
    @8
    @52
    @43
    @44
    @45
    @46
    @49
    @44
    @45
    @46
    @48
    @0
    @6
    @14
    w3a
    @11
    @5
    @6
    w3a
    @14
    @11
    @8
    w3a
    w3a
    @51
    cD
    cE
    cop
    #
    @38
    cop
    @53
    @39
    cop
    cifs
    wbr
    @42
    cD
    cE
    @10
    cC
    cD
    cE
    @10
    @7
    cN
    brifs2
    cD
    cE
    @10
    cC
    cD
    cE
    @10
    @7
    cN
    ifscgr
    sylbird
    syl333anc
    adantr
    mp3and
end
