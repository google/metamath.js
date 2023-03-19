include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "chash.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "crn.mm"
include "wrex.mm"
include "cvv.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "cwlks.mm"
include "wceq.mm"
include "wi.mm"
include "eqid.mm"
include "wlkonprop.mm"
include "c1.mm"
include "cpr.mm"
include "wss.mm"
include "caddc.mm"
include "cfzo.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "wral.mm"
include "wlkvtxiedg.mm"
include "adantr.mm"
include "cn0.mm"
include "wlkcl.mm"
include "cn.mm"
include "elnnne0.mm"
include "simplbi2.mm"
include "lbfzo0.mm"
include "syl6ibr.mm"
include "syl.mm"
include "imp.mm"
include "rspcdva.mm"
include "fvex.mm"
include "prss.mm"
include "eleq1.mm"
include "ax-1.mm"
include "syl6bi.mm"
include "adantl.mm"
include "impd.mm"
include "syl5bir.mm"
include "reximdv.mm"
include "mpd.mm"
include "ex.mm"
include "3adant3.mm"
include "3ad2ant3.mm"

theorem wlkonl1iedg
  let cA: class A
  let cB: class B
  let cP: class P
  let ve: setvar e
  let cF: class F
  let cG: class G
  let cI: class I
  let vk: setvar k
  assume wlkonl1iedg.i: |- I = ( iEdg ` G )

  disjoint A e
  disjoint F e
  disjoint G e
  disjoint I e
  disjoint P e
  disjoint A k
  disjoint e k
  disjoint F k
  disjoint G k
  disjoint I k
  disjoint P k
  assert |- ( ( F ( A ( WalksOn ` G ) B ) P /\ ( # ` F ) =/= 0 ) -> E. e e. ran I A e. e )

  proof
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    chash
    cfv
    #
    cc0
    wne
    #
    cA
    ve
    cv
    #
    wcel
    #
    ve
    cI
    crn
    #
    wrex
    #
    @0
    cG
    cvv
    wcel
    cA
    cG
    cvtx
    cfv
    #
    wcel
    cB
    @7
    wcel
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    @1
    cP
    cfv
    cB
    wceq
    #
    w3a
    #
    w3a
    @2
    @6
    wi
    #
    cA
    cB
    cP
    cF
    cG
    @7
    @7
    eqid
    wlkonprop
    @14
    @8
    @15
    @9
    @10
    @12
    @15
    @13
    @10
    @12
    wa
    #
    @2
    @6
    @16
    @2
    wa
    #
    @11
    c1
    cP
    cfv
    #
    cpr
    #
    @3
    wss
    #
    ve
    @5
    wrex
    #
    @6
    @17
    vk
    cv
    #
    cP
    cfv
    #
    @22
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @3
    wss
    #
    ve
    @5
    wrex
    #
    @21
    vk
    cc0
    @1
    cfzo
    co
    #
    cc0
    @22
    cc0
    wceq
    #
    @27
    @20
    ve
    @5
    @30
    @26
    @19
    @3
    @30
    @23
    @11
    @25
    @18
    @22
    cc0
    cP
    fveq2
    @30
    @24
    c1
    cP
    @30
    @24
    cc0
    c1
    caddc
    co
    c1
    @22
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    sseq1d
    rexbidv
    @16
    @28
    vk
    @29
    wral
    #
    @2
    @10
    @31
    @12
    cP
    ve
    vk
    cF
    cG
    cI
    wlkonl1iedg.i
    wlkvtxiedg
    adantr
    adantr
    @16
    @2
    cc0
    @29
    wcel
    #
    @10
    @2
    @32
    wi
    #
    @12
    @10
    @1
    cn0
    wcel
    #
    @33
    cP
    cF
    cG
    wlkcl
    @34
    @2
    @1
    cn
    wcel
    #
    @32
    @35
    @34
    @2
    @1
    elnnne0
    simplbi2
    @1
    lbfzo0
    syl6ibr
    syl
    adantr
    imp
    rspcdva
    @16
    @21
    @6
    wi
    @2
    @16
    @20
    @4
    ve
    @5
    @20
    @11
    @3
    wcel
    #
    @18
    @3
    wcel
    #
    wa
    @16
    @4
    @11
    @18
    @3
    cc0
    cP
    fvex
    c1
    cP
    fvex
    prss
    @16
    @36
    @37
    @4
    @12
    @36
    @37
    @4
    wi
    #
    wi
    @10
    @12
    @36
    @4
    @38
    @11
    cA
    @3
    eleq1
    @4
    @37
    ax-1
    syl6bi
    adantl
    impd
    syl5bir
    reximdv
    adantr
    mpd
    ex
    3adant3
    3ad2ant3
    syl
    imp
end
