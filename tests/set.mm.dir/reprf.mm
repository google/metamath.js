include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "wcel.mm"
include "wf.mm"
include "crepr.mm"
include "reprval.mm"
include "eleqtrd.mm"
include "elrabi.mm"
include "elmapi.mm"
include "3syl.mm"

theorem reprf
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let cM: class M
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let vm: setvar m
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume reprf.c: |- ( ph -> C e. ( A ( repr ` S ) M ) )


  assert |- ( ph -> C : ( 0 ..^ S ) --> A )

  proof
    wph
    cC
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    vc
    cv
    cfv
    va
    csu
    cM
    wceq
    #
    vc
    cA
    @0
    cmap
    co
    #
    crab
    #
    wcel
    cC
    @2
    wcel
    @0
    cA
    cC
    wf
    wph
    cC
    cA
    cM
    cS
    crepr
    cfv
    co
    @3
    reprf.c
    wph
    cA
    cS
    cM
    va
    vc
    reprval.a
    reprval.m
    reprval.s
    reprval
    eleqtrd
    @1
    vc
    cC
    @2
    elrabi
    cC
    cA
    @0
    elmapi
    3syl
end
