include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "cun.mm"
include "wss.mm"
include "wi.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "ssun1.mm"
include "cnvun.mm"
include "imaeq1i.mm"
include "imaundir.mm"
include "eqtri.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "wceq.mm"
include "suppimacnv.mm"
include "adantr.mm"
include "unexg.mm"
include "adantlr.mm"
include "sylan2.mm"
include "simplr.mm"
include "syl2anc.mm"
include "3sstr4d.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "supp0prc.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem suppun
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z
  assume suppun.g: |- ( ph -> G e. V )


  assert |- ( ph -> ( F supp Z ) C_ ( ( F u. G ) supp Z ) )

  proof
    cF
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    wph
    cF
    cZ
    csupp
    co
    #
    cF
    cG
    cun
    #
    cZ
    csupp
    co
    #
    wss
    #
    wi
    @2
    wph
    @6
    @2
    wph
    wa
    #
    cF
    ccnv
    #
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    @4
    ccnv
    #
    @9
    cima
    #
    @3
    @5
    @10
    @12
    wss
    @7
    @10
    @10
    cG
    ccnv
    #
    @9
    cima
    #
    cun
    #
    @12
    @10
    @14
    ssun1
    @12
    @8
    @13
    cun
    #
    @9
    cima
    @15
    @11
    @16
    @9
    cF
    cG
    cnvun
    imaeq1i
    @8
    @13
    @9
    imaundir
    eqtri
    sseqtr4i
    a1i
    @2
    @3
    @10
    wceq
    wph
    cF
    cvv
    cvv
    cZ
    suppimacnv
    adantr
    @7
    @4
    cvv
    wcel
    #
    @1
    @5
    @12
    wceq
    wph
    @2
    cG
    cV
    wcel
    #
    @17
    suppun.g
    @0
    @18
    @17
    @1
    cF
    cG
    cvv
    cV
    unexg
    adantlr
    sylan2
    @0
    @1
    wph
    simplr
    @4
    cvv
    cvv
    cZ
    suppimacnv
    syl2anc
    3sstr4d
    ex
    @2
    wn
    #
    @6
    wph
    @19
    @3
    c0
    @5
    cF
    cZ
    supp0prc
    @5
    0ss
    syl6eqss
    a1d
    pm2.61i
end
