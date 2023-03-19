include "cc.mm"
include "wcel.mm"
include "ceu.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "ere.mm"
include "recni.mm"
include "epos.mm"
include "gt0ne0ii.mm"
include "cxpef.mm"
include "mp3an12.mm"
include "c1.mm"
include "loge.mm"
include "oveq2i.mm"
include "mulid1.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem ecxp
  let cA: class A


  assert |- ( A e. CC -> ( _e ^c A ) = ( exp ` A ) )

  proof
    cA
    cc
    wcel
    #
    ceu
    cA
    ccxp
    co
    #
    cA
    ceu
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cA
    ce
    cfv
    ceu
    cc
    wcel
    ceu
    cc0
    wne
    @0
    @1
    @4
    wceq
    ceu
    ere
    recni
    ceu
    ere
    epos
    gt0ne0ii
    ceu
    cA
    cxpef
    mp3an12
    @0
    @3
    cA
    ce
    @0
    @3
    cA
    c1
    cmul
    co
    cA
    @2
    c1
    cA
    cmul
    loge
    oveq2i
    cA
    mulid1
    syl5eq
    fveq2d
    eqtrd
end
