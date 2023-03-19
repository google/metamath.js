include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "ceu.mm"
include "clogb.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "c1.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "ere.mm"
include "recni.mm"
include "ene0.mm"
include "ene1.mm"
include "eldifpr.mm"
include "mpbir3an.mm"
include "logbval.mm"
include "mpan.mm"
include "loge.mm"
include "oveq2i.mm"
include "wa.mm"
include "eldifsn.mm"
include "logcl.mm"
include "sylbi.mm"
include "div1d.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem elogb
  let cA: class A


  assert |- ( A e. ( CC \ { 0 } ) -> ( _e logb A ) = ( log ` A ) )

  proof
    cA
    cc
    cc0
    csn
    cdif
    wcel
    #
    ceu
    cA
    clogb
    co
    #
    cA
    clog
    cfv
    #
    ceu
    clog
    cfv
    #
    cdiv
    co
    #
    @2
    ceu
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    @0
    @1
    @4
    wceq
    @5
    ceu
    cc
    wcel
    ceu
    cc0
    wne
    ceu
    c1
    wne
    ceu
    ere
    recni
    ene0
    ene1
    ceu
    cc
    cc0
    c1
    eldifpr
    mpbir3an
    ceu
    cA
    logbval
    mpan
    @0
    @4
    @2
    c1
    cdiv
    co
    @2
    @3
    c1
    @2
    cdiv
    loge
    oveq2i
    @0
    @2
    @0
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    @2
    cc
    wcel
    cA
    cc
    cc0
    eldifsn
    cA
    logcl
    sylbi
    div1d
    syl5eq
    eqtrd
end
