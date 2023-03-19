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
include "simp33.mm"
include "simp32.mm"
include "simp2r3.mm"
include "simp2l2.mm"
include "simp2r1.mm"
include "simp31.mm"
include "simpr3r.mm"
include "ad2antll.mm"
include "btwnconn1lem8.mm"
include "cgrtrand.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "3jca.mm"
include "simpl.mm"
include "simprl.mm"
include "jca.mm"
include "btwnconn1lem6.mm"
include "syl2an.mm"
include "cgrtr3and.mm"

theorem btwnconn1lem9
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


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\ ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\ ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\ ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\ ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\ ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) -> <. R , Q >. Cgr <. E , D >. )

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
    cE
    cD
    @10
    cop
    cbtwn
    wbr
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
    cR
    cQ
    cE
    cD
    cE
    @10
    cN
    @0
    @2
    @3
    @16
    @20
    simp11
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
    @37
    @11
    @13
    @14
    @9
    @4
    @20
    simp2r1
    #
    @21
    @33
    cR
    cQ
    cR
    cP
    cE
    @10
    cN
    @34
    @35
    @36
    @35
    @4
    @16
    @17
    @18
    @19
    simp31
    @37
    @38
    @32
    @30
    @21
    @25
    @29
    @30
    @27
    @28
    @26
    simpr3r
    ad2antll
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
    cgrtrand
    @21
    @4
    @9
    @15
    w3a
    @25
    @26
    wa
    cE
    cD
    cop
    cE
    @10
    cop
    ccgr
    wbr
    @33
    @21
    @4
    @9
    @15
    @4
    @16
    @20
    simp1
    @4
    @9
    @15
    @20
    simp2l
    @4
    @9
    @15
    @20
    simp2r
    3jca
    @33
    @25
    @26
    @25
    @32
    simpl
    @25
    @26
    @31
    simprl
    jca
    cA
    cB
    cC
    cD
    cE
    cN
    vb
    vc
    vd
    btwnconn1lem6
    syl2an
    cgrtr3and
end
