include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "simp11.mm"
include "simp13.mm"
include "simp21.mm"
include "simp3l.mm"
include "simp3r.mm"
include "simp23.mm"
include "simp22.mm"
include "simp1rl.mm"
include "simp2rl.mm"
include "jca.mm"
include "adantl.mm"
include "wi.mm"
include "simp12.mm"
include "btwnexch3.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mpd.mm"
include "simp2ll.mm"
include "simp3ll.mm"
include "btwncomand.mm"
include "simp3lr.mm"
include "wb.mm"
include "cgrcomlr.mm"
include "cgrcom.mm"
include "bitrd.mm"
include "mpbid.mm"
include "simp2rr.mm"
include "simp2lr.mm"
include "cgrcomland.mm"
include "cgrtr3and.mm"
include "cgrextendand.mm"

theorem btwnconn1lem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) ) ) /\ ( ( ( A =/= B /\ B =/= C ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) ) -> <. B , d >. Cgr <. b , D >. )

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
    wa
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
    @21
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
    #
    cbtwn
    wbr
    #
    @7
    @12
    cop
    cC
    cB
    cop
    ccgr
    wbr
    #
    wa
    @10
    @28
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
    #
    wa
    #
    w3a
    #
    cB
    cC
    @10
    @12
    @7
    cD
    cN
    @0
    @2
    @3
    @9
    @14
    simp11
    #
    @0
    @2
    @3
    @9
    @14
    simp13
    #
    @4
    @5
    @6
    @8
    @14
    simp21
    #
    @4
    @9
    @11
    @13
    simp3l
    #
    @4
    @9
    @11
    @13
    simp3r
    #
    @4
    @5
    @6
    @8
    @14
    simp23
    #
    @4
    @5
    @6
    @8
    @14
    simp22
    #
    @15
    @33
    wa
    #
    @17
    @24
    wa
    #
    cC
    cB
    @10
    cop
    cbtwn
    wbr
    #
    @33
    @42
    @15
    @33
    @17
    @24
    @17
    @18
    @16
    @27
    @32
    simp1rl
    @24
    @25
    @23
    @19
    @32
    simp2rl
    jca
    adantl
    @15
    @42
    @43
    wi
    #
    @33
    @15
    @0
    @2
    @3
    @5
    @11
    @44
    @34
    @0
    @2
    @3
    @9
    @14
    simp12
    #
    @35
    @36
    @37
    cA
    cB
    cC
    @10
    cN
    btwnexch3
    syl122anc
    adantr
    mpd
    @15
    @33
    @7
    cD
    @12
    cN
    @34
    @39
    @40
    @38
    @41
    @20
    @29
    wa
    #
    @7
    cD
    @12
    cop
    cbtwn
    wbr
    #
    @33
    @46
    @15
    @33
    @20
    @29
    @20
    @22
    @26
    @19
    @32
    simp2ll
    @29
    @30
    @31
    @19
    @27
    simp3ll
    jca
    adantl
    @15
    @46
    @47
    wi
    #
    @33
    @15
    @0
    @2
    @6
    @8
    @13
    @48
    @34
    @45
    @40
    @39
    @38
    cA
    cD
    @7
    @12
    cN
    btwnexch3
    syl122anc
    adantr
    mpd
    btwncomand
    @41
    @30
    cB
    cC
    cop
    #
    @12
    @7
    cop
    #
    ccgr
    wbr
    #
    @33
    @30
    @15
    @29
    @30
    @31
    @19
    @27
    simp3lr
    adantl
    @15
    @30
    @51
    wb
    @33
    @15
    @30
    @50
    @49
    ccgr
    wbr
    #
    @51
    @15
    @0
    @8
    @13
    @5
    @3
    @30
    @52
    wb
    @34
    @39
    @38
    @36
    @35
    @7
    @12
    cC
    cB
    cN
    cgrcomlr
    syl122anc
    @15
    @0
    @13
    @8
    @3
    @5
    @52
    @51
    wb
    @34
    @38
    @39
    @35
    @36
    @12
    @7
    cB
    cC
    cN
    cgrcom
    syl122anc
    bitrd
    adantr
    mpbid
    @15
    @33
    cC
    @10
    @7
    cD
    cC
    cD
    cN
    @34
    @36
    @37
    @39
    @40
    @36
    @40
    @33
    @25
    @15
    @24
    @25
    @23
    @19
    @32
    simp2rr
    adantl
    @15
    @33
    cD
    @7
    cC
    cD
    cN
    @34
    @40
    @39
    @36
    @40
    @33
    @22
    @15
    @20
    @22
    @26
    @19
    @32
    simp2lr
    adantl
    cgrcomland
    cgrtr3and
    cgrextendand
end
