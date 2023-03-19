include "cc.mm"
include "wss.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "ccncf.mm"
include "wcel.mm"
include "wa.mm"
include "ssel2.mm"
include "mulm1d.mm"
include "mpteq2dva.mm"
include "syl6eqr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "mulcn.mm"
include "a1i.mm"
include "neg1cn.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "mp3an13.mm"
include "cncfmptid.mm"
include "mpan2.mm"
include "cncfmpt2f.mm"
include "eqeltrrd.mm"

theorem negcncf
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume negcncf.1: |- F = ( x e. A |-> -u x )

  disjoint A x
  assert |- ( A C_ CC -> F e. ( A -cn-> CC ) )

  proof
    cA
    cc
    wss
    #
    vx
    cA
    c1
    cneg
    #
    vx
    cv
    #
    cmul
    co
    #
    cmpt
    #
    cF
    cA
    cc
    ccncf
    co
    #
    @0
    @4
    vx
    cA
    @2
    cneg
    #
    cmpt
    cF
    @0
    vx
    cA
    @3
    @6
    @0
    @2
    cA
    wcel
    wa
    @2
    cA
    cc
    @2
    ssel2
    mulm1d
    mpteq2dva
    negcncf.1
    syl6eqr
    @0
    vx
    @1
    @2
    cmul
    ccnfld
    ctopn
    cfv
    #
    cA
    @7
    eqid
    #
    cmul
    @7
    @7
    ctx
    co
    @7
    ccn
    co
    wcel
    @0
    @7
    @8
    mulcn
    a1i
    @1
    cc
    wcel
    @0
    cc
    cc
    wss
    #
    vx
    cA
    @1
    cmpt
    @5
    wcel
    neg1cn
    cc
    ssid
    #
    vx
    @1
    cA
    cc
    cncfmptc
    mp3an13
    @0
    @9
    vx
    cA
    @2
    cmpt
    @5
    wcel
    @10
    vx
    cA
    cc
    cncfmptid
    mpan2
    cncfmpt2f
    eqeltrrd
end
