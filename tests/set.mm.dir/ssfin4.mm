include "cfin4.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "wex.mm"
include "wn.mm"
include "simpll.mm"
include "cdif.mm"
include "cun.mm"
include "wceq.mm"
include "pssss.mm"
include "simpr.mm"
include "sylan9ssr.mm"
include "difssd.mm"
include "unssd.mm"
include "pssnel.mm"
include "adantl.mm"
include "simpllr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "elndif.mm"
include "ad2antrl.mm"
include "wo.mm"
include "ioran.mm"
include "elun.mm"
include "xchnxbir.mm"
include "sylanbrc.mm"
include "nelneq2.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "sylnib.mm"
include "exlimddv.mm"
include "dfpss2.mm"
include "adantrr.mm"
include "cin.mm"
include "c0.mm"
include "cvv.mm"
include "difexg.mm"
include "enrefg.mm"
include "3syl.mm"
include "ssinss1.mm"
include "syl.mm"
include "inssdif0.mm"
include "sylib.mm"
include "disjdif.mm"
include "jctir.mm"
include "unen.mm"
include "syl21anc.mm"
include "simplr.mm"
include "undif.mm"
include "breqtrd.mm"
include "fin4i.mm"
include "pm2.65da.mm"
include "nexdv.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "isfin4.mm"
include "mpbird.mm"

theorem ssfin4
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x


  assert |- ( ( A e. Fin4 /\ B C_ A ) -> B e. Fin4 )

  proof
    cA
    cfin4
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cB
    cfin4
    wcel
    #
    vx
    cv
    #
    cB
    wpss
    #
    @4
    cB
    cen
    wbr
    #
    wa
    #
    vx
    wex
    wn
    #
    @2
    @7
    vx
    @2
    @7
    @0
    @0
    @1
    @7
    simpll
    #
    @2
    @7
    wa
    #
    @4
    cA
    cB
    cdif
    #
    cun
    #
    cA
    wpss
    #
    @12
    cA
    cen
    wbr
    @0
    wn
    @2
    @5
    @13
    @6
    @2
    @5
    wa
    #
    @12
    cA
    wss
    @12
    cA
    wceq
    #
    wn
    #
    @13
    @14
    @4
    @11
    cA
    @5
    @2
    @4
    cB
    cA
    @4
    cB
    pssss
    #
    @0
    @1
    simpr
    sylan9ssr
    @14
    cA
    cB
    difssd
    unssd
    @14
    vc
    cv
    #
    cB
    wcel
    #
    @18
    @4
    wcel
    #
    wn
    #
    wa
    #
    @16
    vc
    @5
    @22
    vc
    wex
    @2
    vc
    @4
    cB
    pssnel
    adantl
    @14
    @22
    wa
    #
    cA
    @12
    wceq
    #
    @15
    @23
    @18
    cA
    wcel
    @18
    @12
    wcel
    #
    wn
    #
    @24
    wn
    @23
    cB
    cA
    @18
    @0
    @1
    @5
    @22
    simpllr
    @14
    @19
    @21
    simprl
    sseldd
    @23
    @21
    @18
    @11
    wcel
    #
    wn
    #
    @26
    @14
    @19
    @21
    simprr
    @19
    @28
    @14
    @21
    @18
    cB
    cA
    elndif
    ad2antrl
    @20
    @27
    wo
    @21
    @28
    wa
    @25
    @20
    @27
    ioran
    @18
    @4
    @11
    elun
    xchnxbir
    sylanbrc
    @18
    cA
    @12
    nelneq2
    syl2anc
    cA
    @12
    eqcom
    sylnib
    exlimddv
    @12
    cA
    dfpss2
    sylanbrc
    adantrr
    @10
    @12
    cB
    @11
    cun
    #
    cA
    cen
    @10
    @6
    @11
    @11
    cen
    wbr
    #
    @4
    @11
    cin
    c0
    wceq
    #
    cB
    @11
    cin
    c0
    wceq
    #
    wa
    @12
    @29
    cen
    wbr
    @2
    @5
    @6
    simprr
    @10
    @0
    @11
    cvv
    wcel
    @30
    @9
    cA
    cB
    cfin4
    difexg
    @11
    cvv
    enrefg
    3syl
    @10
    @31
    @32
    @10
    @4
    cA
    cin
    cB
    wss
    #
    @31
    @10
    @4
    cB
    wss
    #
    @33
    @5
    @34
    @2
    @6
    @17
    ad2antrl
    @4
    cA
    cB
    ssinss1
    syl
    @4
    cA
    cB
    inssdif0
    sylib
    cB
    cA
    disjdif
    jctir
    @4
    cB
    @11
    @11
    unen
    syl21anc
    @10
    @1
    @29
    cA
    wceq
    @0
    @1
    @7
    simplr
    cB
    cA
    undif
    sylib
    breqtrd
    cA
    @12
    fin4i
    syl2anc
    pm2.65da
    nexdv
    @2
    cB
    cvv
    wcel
    #
    @3
    @8
    wb
    @1
    @0
    @35
    cB
    cA
    cfin4
    ssexg
    ancoms
    vx
    cB
    cvv
    isfin4
    syl
    mpbird
end
