include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "simp11.mm"
include "simp13.mm"
include "simp22.mm"
include "simp23.mm"
include "simp33.mm"
include "simp31.mm"
include "simp21.mm"
include "simp12.mm"
include "simp1rr.mm"
include "adantl.mm"
include "simp2ll.mm"
include "btwnexch3and.mm"
include "simp2rl.mm"
include "simp3rl.mm"
include "btwncomand.mm"
include "simp3rr.mm"
include "cgrcomand.mm"
include "cgrcomlrand.mm"
include "simp2lr.mm"
include "simp2rr.mm"
include "cgrcomland.mm"
include "cgrtr3and.mm"
include "cgrextendand.mm"

theorem btwnconn1lem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let cX: class X
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ X e. ( EE ` N ) ) ) /\ ( ( ( A =/= B /\ B =/= C ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , X >. /\ <. d , X >. Cgr <. D , B >. ) ) ) ) -> <. B , c >. Cgr <. X , C >. )

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
    cX
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
    wa
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cB
    cA
    cD
    cop
    cbtwn
    wbr
    #
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
    @22
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    @7
    cA
    @12
    cop
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
    #
    @10
    cA
    cX
    cop
    cbtwn
    wbr
    #
    @10
    cX
    cop
    cD
    cB
    cop
    ccgr
    wbr
    #
    wa
    wa
    #
    w3a
    #
    cB
    cD
    @7
    cX
    @10
    cC
    cN
    @0
    @2
    @3
    @9
    @15
    simp11
    #
    @0
    @2
    @3
    @9
    @15
    simp13
    #
    @4
    @5
    @6
    @8
    @15
    simp22
    #
    @4
    @5
    @6
    @8
    @15
    simp23
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
    @4
    @5
    @6
    @8
    @15
    simp21
    #
    @16
    @33
    cA
    cB
    cD
    @7
    cN
    @34
    @0
    @2
    @3
    @9
    @15
    simp12
    #
    @35
    @36
    @37
    @33
    @19
    @16
    @18
    @19
    @17
    @28
    @32
    simp1rr
    adantl
    @33
    @21
    @16
    @21
    @23
    @27
    @20
    @32
    simp2ll
    adantl
    btwnexch3and
    @16
    @33
    @10
    cC
    cX
    cN
    @34
    @39
    @40
    @38
    @16
    @33
    cA
    cC
    @10
    cX
    cN
    @34
    @41
    @40
    @39
    @38
    @33
    @25
    @16
    @25
    @26
    @24
    @20
    @32
    simp2rl
    adantl
    @33
    @30
    @16
    @30
    @31
    @29
    @20
    @28
    simp3rl
    adantl
    btwnexch3and
    btwncomand
    @16
    @33
    cD
    cB
    @10
    cX
    cN
    @34
    @36
    @35
    @39
    @38
    @16
    @33
    @10
    cX
    cD
    cB
    cN
    @34
    @39
    @38
    @36
    @35
    @33
    @31
    @16
    @30
    @31
    @29
    @20
    @28
    simp3rr
    adantl
    cgrcomand
    cgrcomlrand
    @16
    @33
    cD
    @7
    @10
    cC
    cC
    cD
    cN
    @34
    @36
    @37
    @39
    @40
    @40
    @36
    @33
    @23
    @16
    @21
    @23
    @27
    @20
    @32
    simp2lr
    adantl
    @16
    @33
    cC
    @10
    cC
    cD
    cN
    @34
    @40
    @39
    @40
    @36
    @33
    @26
    @16
    @25
    @26
    @24
    @20
    @32
    simp2rr
    adantl
    cgrcomland
    cgrtr3and
    cgrextendand
end
