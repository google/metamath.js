include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "crn.mm"
include "wss.mm"
include "ccom.mm"
include "cima.mm"
include "wceq.mm"
include "wi.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "imaeq2i.mm"
include "cdm.mm"
include "wfo.mm"
include "funforn.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "anim2i.mm"
include "ancomd.mm"
include "suppimacnv.mm"
include "syl.mm"
include "sseq1d.mm"
include "biimpd.mm"
include "adantld.mm"
include "imp.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "coexg.mm"
include "imaeq2d.mm"
include "adantr.mm"
include "3eqtr4d.mm"
include "exp31.mm"
include "wn.mm"
include "c0.mm"
include "ima0.mm"
include "id.mm"
include "intnand.mm"
include "supp0prc.mm"
include "3eqtr4a.mm"
include "2a1d.mm"
include "pm2.61i.mm"

theorem imacosupp
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z


  assert |- ( ( F e. V /\ G e. W ) -> ( ( Fun G /\ ( F supp Z ) C_ ran G ) -> ( G " ( ( F o. G ) supp Z ) ) = ( F supp Z ) ) )

  proof
    cZ
    cvv
    wcel
    #
    cF
    cV
    wcel
    #
    cG
    cW
    wcel
    #
    wa
    #
    cG
    wfun
    #
    cF
    cZ
    csupp
    co
    #
    cG
    crn
    #
    wss
    #
    wa
    #
    cG
    cF
    cG
    ccom
    #
    cZ
    csupp
    co
    #
    cima
    #
    @5
    wceq
    #
    wi
    wi
    @0
    @3
    @8
    @12
    @0
    @3
    wa
    #
    @8
    wa
    #
    cG
    @9
    ccnv
    #
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cima
    #
    cF
    ccnv
    #
    @16
    cima
    #
    @11
    @5
    @14
    @18
    cG
    cG
    ccnv
    #
    @20
    cima
    #
    cima
    #
    @20
    @17
    @22
    cG
    @17
    @21
    @19
    ccom
    #
    @16
    cima
    @22
    @15
    @24
    @16
    cF
    cG
    cnvco
    imaeq1i
    @21
    @19
    @16
    imaco
    eqtri
    imaeq2i
    @14
    cG
    cdm
    #
    @6
    cG
    wfo
    #
    @20
    @6
    wss
    #
    @23
    @20
    wceq
    @4
    @26
    @13
    @7
    @4
    @26
    cG
    funforn
    biimpi
    ad2antrl
    @13
    @8
    @27
    @13
    @7
    @27
    @4
    @13
    @7
    @27
    @13
    @5
    @20
    @6
    @13
    @1
    @0
    wa
    @5
    @20
    wceq
    #
    @13
    @0
    @1
    @3
    @1
    @0
    @1
    @2
    simpl
    anim2i
    ancomd
    cF
    cV
    cvv
    cZ
    suppimacnv
    syl
    #
    sseq1d
    biimpd
    adantld
    imp
    @25
    @6
    @20
    cG
    foimacnv
    syl2anc
    syl5eq
    @13
    @11
    @18
    wceq
    @8
    @13
    @10
    @17
    cG
    @13
    @9
    cvv
    wcel
    #
    @0
    wa
    #
    @10
    @17
    wceq
    @13
    @0
    @30
    @3
    @30
    @0
    cF
    cG
    cV
    cW
    coexg
    anim2i
    ancomd
    @9
    cvv
    cvv
    cZ
    suppimacnv
    syl
    imaeq2d
    adantr
    @13
    @28
    @8
    @29
    adantr
    3eqtr4d
    exp31
    @0
    wn
    #
    @12
    @3
    @8
    @32
    cG
    c0
    cima
    c0
    @11
    @5
    cG
    ima0
    @32
    @10
    c0
    cG
    @32
    @31
    wn
    @10
    c0
    wceq
    @32
    @0
    @30
    @32
    id
    #
    intnand
    @9
    cZ
    supp0prc
    syl
    imaeq2d
    @32
    cF
    cvv
    wcel
    #
    @0
    wa
    wn
    @5
    c0
    wceq
    @32
    @0
    @34
    @33
    intnand
    cF
    cZ
    supp0prc
    syl
    3eqtr4a
    2a1d
    pm2.61i
end
