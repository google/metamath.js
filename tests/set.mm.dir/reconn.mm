include "cr.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "wcel.mm"
include "cv.mm"
include "cicc.mm"
include "wral.mm"
include "wa.mm"
include "reconnlem1.mm"
include "ralrimivva.mm"
include "ex.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "w3a.mm"
include "cun.mm"
include "wn.mm"
include "wi.mm"
include "wex.mm"
include "n0.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "simplll.mm"
include "inss2.mm"
include "simprll.mm"
include "sseldi.mm"
include "sseldd.mm"
include "simprlr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "csup.mm"
include "adantr.mm"
include "simplrl.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "simpllr.mm"
include "simpr.mm"
include "eqid.mm"
include "reconnlem2.mm"
include "incom.mm"
include "syl5eqss.mm"
include "uncom.mm"
include "sseq2i.mm"
include "sylnib.mm"
include "lecasei.mm"
include "exp32.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "syl5bi.mm"
include "expd.mm"
include "3impd.mm"
include "ralrimdvva.mm"
include "ctopon.mm"
include "wb.mm"
include "retopon.mm"
include "connsub.mm"
include "mpan.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem reconn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  assert |- ( A C_ RR -> ( ( ( topGen ` ran (,) ) |`t A ) e. Conn <-> A. x e. A A. y e. A ( x [,] y ) C_ A ) )

  proof
    cA
    cr
    wss
    #
    cioo
    crn
    ctg
    cfv
    #
    cA
    crest
    co
    cconn
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cicc
    co
    cA
    wss
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @0
    @2
    @6
    @0
    @2
    wa
    @5
    vx
    vy
    cA
    cA
    cA
    @3
    @4
    reconnlem1
    ralrimivva
    ex
    @0
    @6
    vu
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    vv
    cv
    #
    cA
    cin
    #
    c0
    wne
    #
    @7
    @10
    cin
    #
    cr
    cA
    cdif
    #
    wss
    #
    w3a
    cA
    @7
    @10
    cun
    #
    wss
    #
    wn
    #
    wi
    #
    vv
    @1
    wral
    vu
    @1
    wral
    #
    @2
    @0
    @6
    @19
    vu
    vv
    @1
    @1
    @0
    @7
    @1
    wcel
    #
    @10
    @1
    wcel
    #
    wa
    #
    wa
    #
    @6
    @19
    @24
    @6
    wa
    #
    @9
    @12
    @15
    @18
    @25
    @9
    @12
    @15
    @18
    wi
    #
    @9
    @12
    wa
    vb
    cv
    #
    @8
    wcel
    #
    vb
    wex
    #
    vc
    cv
    #
    @11
    wcel
    #
    vc
    wex
    #
    wa
    #
    @25
    @26
    @9
    @29
    @12
    @32
    vb
    @8
    n0
    vc
    @11
    n0
    anbi12i
    @33
    @28
    @31
    wa
    #
    vc
    wex
    vb
    wex
    @25
    @26
    @28
    @31
    vb
    vc
    eeanv
    @25
    @34
    @26
    vb
    vc
    @25
    @34
    @15
    @18
    @25
    @34
    @15
    wa
    #
    wa
    #
    @18
    @27
    @30
    @36
    cA
    cr
    @27
    @0
    @23
    @6
    @35
    simplll
    #
    @36
    @8
    cA
    @27
    @7
    cA
    inss2
    @25
    @28
    @31
    @15
    simprll
    #
    sseldi
    sseldd
    @36
    cA
    cr
    @30
    @37
    @36
    @11
    cA
    @30
    @10
    cA
    inss2
    @25
    @28
    @31
    @15
    simprlr
    #
    sseldi
    sseldd
    @36
    @27
    @30
    cle
    wbr
    #
    wa
    vx
    vy
    cA
    @27
    @30
    @7
    @27
    @30
    cicc
    co
    cin
    cr
    clt
    csup
    #
    @7
    @10
    @36
    @0
    @40
    @37
    adantr
    @25
    @21
    @35
    @40
    @0
    @21
    @22
    @6
    simplrl
    #
    ad2antrr
    @25
    @22
    @35
    @40
    @0
    @21
    @22
    @6
    simplrr
    #
    ad2antrr
    @24
    @6
    @35
    @40
    simpllr
    @36
    @28
    @40
    @38
    adantr
    @36
    @31
    @40
    @39
    adantr
    @25
    @34
    @15
    @40
    simplrr
    @36
    @40
    simpr
    @41
    eqid
    reconnlem2
    @36
    @30
    @27
    cle
    wbr
    #
    wa
    #
    cA
    @10
    @7
    cun
    #
    wss
    @17
    @45
    vx
    vy
    cA
    @30
    @27
    @10
    @30
    @27
    cicc
    co
    cin
    cr
    clt
    csup
    #
    @10
    @7
    @36
    @0
    @44
    @37
    adantr
    @25
    @22
    @35
    @44
    @43
    ad2antrr
    @25
    @21
    @35
    @44
    @42
    ad2antrr
    @24
    @6
    @35
    @44
    simpllr
    @36
    @31
    @44
    @39
    adantr
    @36
    @28
    @44
    @38
    adantr
    @45
    @10
    @7
    cin
    @13
    @14
    @10
    @7
    incom
    @25
    @34
    @15
    @44
    simplrr
    syl5eqss
    @36
    @44
    simpr
    @47
    eqid
    reconnlem2
    @46
    @16
    cA
    @10
    @7
    uncom
    sseq2i
    sylnib
    lecasei
    exp32
    exlimdvv
    syl5bir
    syl5bi
    expd
    3impd
    ex
    ralrimdvva
    @1
    cr
    ctopon
    cfv
    wcel
    @0
    @2
    @20
    wb
    retopon
    vu
    vv
    cA
    @1
    cr
    connsub
    mpan
    sylibrd
    impbid
end
