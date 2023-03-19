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
include "simp2r1.mm"
include "simp2r3.mm"
include "simp2l2.mm"
include "simp31.mm"
include "simp33.mm"
include "simp32.mm"
include "simprlr.mm"
include "adantl.mm"
include "btwncomand.mm"
include "simpr3l.mm"
include "ad2antll.mm"
include "btwnconn1lem8.mm"
include "wb.mm"
include "cgrcomlr.mm"
include "syl122anc.mm"
include "cgrcom.mm"
include "bitrd.mm"
include "adantr.mm"
include "mpbid.mm"
include "btwnconn1lem9.mm"
include "cgrcomand.mm"
include "cgrextendand.mm"

theorem btwnconn1lem10
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\ ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\ ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\ ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\ ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\ ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) -> <. d , D >. Cgr <. P , Q >. )

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
    wa
    #
    cP
    @1
    wcel
    #
    cQ
    @1
    wcel
    #
    cR
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
    cD
    cA
    @7
    cop
    cbtwn
    wbr
    cD
    @7
    cop
    cC
    cD
    cop
    #
    ccgr
    wbr
    wa
    cC
    cA
    @10
    cop
    cbtwn
    wbr
    cC
    @10
    cop
    #
    @22
    ccgr
    wbr
    wa
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
    @24
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
    cC
    @7
    cP
    cop
    cbtwn
    wbr
    cC
    cP
    cop
    @23
    ccgr
    wbr
    wa
    #
    cC
    @10
    cR
    cop
    cbtwn
    wbr
    cC
    cR
    cop
    cC
    cE
    cop
    ccgr
    wbr
    wa
    #
    cR
    cP
    cQ
    cop
    cbtwn
    wbr
    #
    cR
    cQ
    cop
    cR
    cP
    cop
    #
    ccgr
    wbr
    #
    wa
    w3a
    #
    wa
    #
    wa
    #
    @10
    cE
    cD
    cP
    cR
    cQ
    cN
    @0
    @2
    @3
    @16
    @20
    simp11
    #
    @11
    @13
    @14
    @9
    @4
    @20
    simp2r1
    #
    @11
    @13
    @14
    @9
    @4
    @20
    simp2r3
    #
    @5
    @6
    @8
    @15
    @4
    @20
    simp2l2
    #
    @4
    @16
    @17
    @18
    @19
    simp31
    #
    @4
    @16
    @17
    @18
    @19
    simp33
    #
    @4
    @16
    @17
    @18
    @19
    simp32
    #
    @21
    @36
    cE
    cD
    @10
    cN
    @37
    @39
    @40
    @38
    @36
    @27
    @21
    @25
    @26
    @27
    @34
    simprlr
    adantl
    btwncomand
    @35
    @31
    @21
    @25
    @31
    @33
    @29
    @30
    @28
    simpr3l
    ad2antll
    @21
    @36
    wa
    @32
    cE
    @10
    cop
    ccgr
    wbr
    #
    @10
    cE
    cop
    #
    cP
    cR
    cop
    #
    ccgr
    wbr
    #
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cE
    cN
    vb
    vc
    vd
    btwnconn1lem8
    @21
    @44
    @47
    wb
    @36
    @21
    @44
    @46
    @45
    ccgr
    wbr
    #
    @47
    @21
    @0
    @19
    @17
    @14
    @11
    @44
    @48
    wb
    @37
    @42
    @41
    @39
    @38
    cR
    cP
    cE
    @10
    cN
    cgrcomlr
    syl122anc
    @21
    @0
    @17
    @19
    @11
    @14
    @48
    @47
    wb
    @37
    @41
    @42
    @38
    @39
    cP
    cR
    @10
    cE
    cN
    cgrcom
    syl122anc
    bitrd
    adantr
    mpbid
    @21
    @36
    cR
    cQ
    cE
    cD
    cN
    @37
    @42
    @43
    @39
    @40
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cE
    cN
    vb
    vc
    vd
    btwnconn1lem9
    cgrcomand
    cgrextendand
end
