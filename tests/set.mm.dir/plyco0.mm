include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "clt.mm"
include "wn.mm"
include "simprr.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "ffun.mm"
include "adantl.mm"
include "peano2nn0.mm"
include "adantr.mm"
include "eluznn0.mm"
include "ex.mm"
include "syl.mm"
include "ssrdv.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funfvima2.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "peano2zd.mm"
include "ad2antrl.mm"
include "eluz.mm"
include "simplr.mm"
include "eleq2d.mm"
include "fvex.mm"
include "elsn.mm"
include "syl6bb.mm"
include "3imtr3d.mm"
include "necon3ad.mm"
include "mpd.mm"
include "cr.mm"
include "nn0re.mm"
include "zred.mm"
include "ltnled.mm"
include "mpbird.mm"
include "zleltp1.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ccnv.mm"
include "simpr.mm"
include "syl2an.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "eluzle.mm"
include "ad2antll.mm"
include "ltletrd.mm"
include "mpbid.mm"
include "simprl.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "breq1.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "necon1bd.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antlr.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "funimass3.mm"
include "sylan.mm"
include "uzid.mm"
include "eqeltrrd.mm"
include "snssd.mm"
include "eqssd.mm"
include "impbida.mm"

theorem plyco0
  let cA: class A
  let vk: setvar k
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vz: setvar z
  let vf: setvar f
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cF: class F

  disjoint A k
  disjoint N k
  disjoint a k
  disjoint a n
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint A n
  disjoint A z
  disjoint N a
  disjoint N n
  disjoint N z
  disjoint a f
  disjoint a x
  disjoint S a
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f z
  disjoint S f
  disjoint k x
  disjoint S k
  disjoint n x
  disjoint S n
  disjoint x z
  disjoint S x
  disjoint S z
  disjoint T a
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T z
  disjoint F a
  disjoint F f
  disjoint F n
  assert |- ( ( N e. NN0 /\ A : NN0 --> CC ) -> ( ( A " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } <-> A. k e. NN0 ( ( A ` k ) =/= 0 -> k <_ N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cn0
    cc
    cA
    wf
    #
    wa
    #
    cA
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cima
    #
    cc0
    csn
    #
    wceq
    #
    vk
    cv
    #
    cA
    cfv
    #
    cc0
    wne
    #
    @8
    cN
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @2
    @7
    wa
    #
    @12
    vk
    cn0
    @14
    @8
    cn0
    wcel
    #
    @10
    @11
    @14
    @15
    @10
    wa
    #
    wa
    #
    @11
    @8
    @3
    clt
    wbr
    #
    @17
    @18
    @3
    @8
    cle
    wbr
    #
    wn
    #
    @17
    @10
    @20
    @14
    @15
    @10
    simprr
    @17
    @19
    @9
    cc0
    @17
    @8
    @4
    wcel
    #
    @9
    @5
    wcel
    #
    @19
    @9
    cc0
    wceq
    #
    @2
    @21
    @22
    wi
    #
    @7
    @16
    @2
    cA
    wfun
    #
    @4
    cA
    cdm
    #
    wss
    #
    @24
    @1
    @25
    @0
    cn0
    cc
    cA
    ffun
    adantl
    #
    @2
    @4
    cn0
    @26
    @2
    vk
    @4
    cn0
    @2
    @3
    cn0
    wcel
    #
    @21
    @15
    wi
    @0
    @29
    @1
    cN
    peano2nn0
    adantr
    #
    @29
    @21
    @15
    @8
    @3
    eluznn0
    ex
    syl
    ssrdv
    @1
    @26
    cn0
    wceq
    @0
    cn0
    cc
    cA
    fdm
    adantl
    sseqtr4d
    #
    @4
    @8
    cA
    funfvima2
    syl2anc
    ad2antrr
    @17
    @3
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @21
    @19
    wb
    @2
    @32
    @7
    @16
    @2
    cN
    @0
    cN
    cz
    wcel
    #
    @1
    cN
    nn0z
    adantr
    #
    peano2zd
    #
    ad2antrr
    @15
    @33
    @14
    @10
    @8
    nn0z
    ad2antrl
    #
    @3
    @8
    eluz
    syl2anc
    @17
    @22
    @9
    @6
    wcel
    @23
    @17
    @5
    @6
    @9
    @2
    @7
    @16
    simplr
    eleq2d
    @9
    cc0
    @8
    cA
    fvex
    elsn
    syl6bb
    3imtr3d
    necon3ad
    mpd
    @17
    @8
    @3
    @15
    @8
    cr
    wcel
    @14
    @10
    @8
    nn0re
    ad2antrl
    @2
    @3
    cr
    wcel
    #
    @7
    @16
    @2
    @3
    @36
    zred
    #
    ad2antrr
    ltnled
    mpbird
    @17
    @33
    @34
    @11
    @18
    wb
    @37
    @2
    @34
    @7
    @16
    @35
    ad2antrr
    @8
    cN
    zleltp1
    syl2anc
    mpbird
    expr
    ralrimiva
    @2
    @13
    wa
    #
    @5
    @6
    @40
    @5
    @6
    wss
    #
    @4
    cA
    ccnv
    @6
    cima
    #
    wss
    #
    @40
    vn
    @4
    @42
    @2
    @13
    vn
    cv
    #
    @4
    wcel
    #
    @44
    @42
    wcel
    #
    @2
    @13
    @45
    wa
    #
    wa
    #
    @46
    @44
    cn0
    wcel
    #
    @44
    cA
    cfv
    #
    cc0
    wceq
    #
    @2
    @29
    @45
    @49
    @47
    @30
    @13
    @45
    simpr
    @44
    @3
    eluznn0
    syl2an
    #
    @48
    @44
    cN
    cle
    wbr
    #
    wn
    #
    @51
    @48
    cN
    @44
    clt
    wbr
    @54
    @48
    cN
    @3
    @44
    @2
    cN
    cr
    wcel
    #
    @47
    @0
    @55
    @1
    cN
    nn0re
    adantr
    #
    adantr
    #
    @2
    @38
    @47
    @39
    adantr
    @48
    @44
    @52
    nn0red
    #
    @48
    cN
    @57
    ltp1d
    @45
    @3
    @44
    cle
    wbr
    @2
    @13
    @3
    @44
    eluzle
    ad2antll
    ltletrd
    @48
    cN
    @44
    @57
    @58
    ltnled
    mpbid
    @48
    @53
    @50
    cc0
    @48
    @49
    @13
    @50
    cc0
    wne
    #
    @53
    wi
    #
    @52
    @2
    @13
    @45
    simprl
    @12
    @60
    vk
    @44
    cn0
    @8
    @44
    wceq
    #
    @10
    @59
    @11
    @53
    @61
    @9
    @50
    cc0
    @8
    @44
    cA
    fveq2
    neeq1d
    @8
    @44
    cN
    cle
    breq1
    imbi12d
    rspcva
    syl2anc
    necon1bd
    mpd
    @48
    cA
    cn0
    wfn
    #
    @46
    @49
    @51
    wa
    wb
    @1
    @62
    @0
    @47
    cn0
    cc
    cA
    ffn
    ad2antlr
    cn0
    cc0
    @44
    cA
    fniniseg
    syl
    mpbir2and
    expr
    ssrdv
    @2
    @41
    @43
    wb
    #
    @13
    @2
    @25
    @27
    @63
    @28
    @31
    @4
    @6
    cA
    funimass3
    syl2anc
    adantr
    mpbird
    @40
    cc0
    @5
    @40
    @3
    cA
    cfv
    #
    cc0
    @5
    @40
    @3
    cN
    cle
    wbr
    #
    wn
    #
    @64
    cc0
    wceq
    @2
    @66
    @13
    @2
    cN
    @3
    clt
    wbr
    @66
    @2
    cN
    @56
    ltp1d
    @2
    cN
    @3
    @56
    @39
    ltnled
    mpbid
    adantr
    @40
    @65
    @64
    cc0
    @2
    @29
    @13
    @64
    cc0
    wne
    #
    @65
    wi
    #
    @30
    @12
    @68
    vk
    @3
    cn0
    @8
    @3
    wceq
    #
    @10
    @67
    @11
    @65
    @69
    @9
    @64
    cc0
    @8
    @3
    cA
    fveq2
    neeq1d
    @8
    @3
    cN
    cle
    breq1
    imbi12d
    rspcva
    sylan
    necon1bd
    mpd
    @2
    @64
    @5
    wcel
    #
    @13
    @2
    @3
    @4
    wcel
    #
    @70
    @2
    @32
    @71
    @36
    @3
    uzid
    syl
    @2
    @25
    @27
    @71
    @70
    wi
    @28
    @31
    @4
    @3
    cA
    funfvima2
    syl2anc
    mpd
    adantr
    eqeltrrd
    snssd
    eqssd
    impbida
end
