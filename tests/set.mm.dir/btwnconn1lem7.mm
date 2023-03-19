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
include "simp1l3.mm"
include "adantr.mm"
include "simp2rr.mm"
include "simp2lr.mm"
include "3jca.mm"
include "wi.mm"
include "simp11.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "simpr1.mm"
include "wceq.mm"
include "opeq2.mm"
include "breq1d.mm"
include "3anbi2d.mm"
include "biimparc.mm"
include "simp2.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "cgrid2.mm"
include "syl13anc.mm"
include "syl5.mm"
include "imp.mm"
include "opeq1.mm"
include "breq12d.mm"
include "simp3l.mm"
include "axcgrid.mm"
include "expdimp.mm"
include "3ad2antr3.mm"
include "mpd.mm"
include "ex.mm"
include "necon3d.mm"
include "syl122anc.mm"

theorem btwnconn1lem7
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\ ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\ ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) ) ) -> C =/= d )

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
    #
    cB
    cC
    wne
    #
    cC
    @7
    wne
    #
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
    #
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
    #
    @24
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
    @32
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
    cE
    cD
    @10
    cop
    cbtwn
    wbr
    wa
    #
    wa
    #
    cC
    @10
    wne
    #
    @37
    @19
    @29
    @25
    w3a
    #
    @16
    @38
    @37
    @19
    @29
    @25
    @34
    @19
    @36
    @17
    @18
    @19
    @20
    @31
    @33
    simp1l3
    adantr
    @34
    @29
    @36
    @27
    @29
    @26
    @21
    @33
    simp2rr
    adantr
    @34
    @25
    @36
    @22
    @25
    @30
    @21
    @33
    simp2lr
    adantr
    3jca
    @16
    @0
    @5
    @6
    @8
    @11
    @39
    @38
    wi
    @0
    @2
    @3
    @9
    @15
    simp11
    @4
    @5
    @6
    @8
    @15
    simp21
    @4
    @5
    @6
    @8
    @15
    simp22
    @4
    @5
    @6
    @8
    @15
    simp23
    @4
    @9
    @11
    @13
    @14
    simp31
    @0
    @5
    @6
    wa
    #
    @8
    @11
    wa
    #
    w3a
    #
    @39
    @38
    @42
    @39
    wa
    #
    @19
    @38
    @42
    @19
    @29
    @25
    simpr1
    @43
    cC
    @10
    cC
    @7
    @42
    @39
    cC
    @10
    wceq
    #
    cC
    @7
    wceq
    #
    @39
    @44
    wa
    @19
    cC
    cC
    cop
    #
    @24
    ccgr
    wbr
    #
    @25
    w3a
    #
    @42
    @45
    @44
    @48
    @39
    @44
    @47
    @29
    @19
    @25
    @44
    @46
    @28
    @24
    ccgr
    cC
    @10
    cC
    opeq2
    breq1d
    3anbi2d
    biimparc
    @42
    @48
    @45
    @42
    @48
    wa
    cC
    cD
    wceq
    #
    @45
    @42
    @48
    @49
    @48
    @47
    @42
    @49
    @19
    @47
    @25
    simp2
    @42
    @0
    @5
    @5
    @6
    @47
    @49
    wi
    @0
    @40
    @41
    simp1
    #
    @0
    @5
    @6
    @41
    simp2l
    #
    @51
    @0
    @5
    @6
    @41
    simp2r
    cC
    cC
    cD
    cN
    cgrid2
    syl13anc
    syl5
    imp
    @42
    @19
    @25
    @49
    @45
    wi
    @47
    @42
    @25
    @49
    @45
    @25
    @49
    wa
    @35
    @46
    ccgr
    wbr
    #
    @42
    @45
    @49
    @52
    @25
    @49
    @35
    @23
    @46
    @24
    ccgr
    cC
    cD
    @7
    opeq1
    cC
    cD
    cC
    opeq2
    breq12d
    biimparc
    @42
    @0
    @5
    @8
    @5
    @52
    @45
    wi
    @50
    @51
    @0
    @40
    @8
    @11
    simp3l
    @51
    cC
    @7
    cC
    cN
    axcgrid
    syl13anc
    syl5
    expdimp
    3ad2antr3
    mpd
    ex
    syl5
    expdimp
    necon3d
    mpd
    ex
    syl122anc
    syl5
    imp
end
