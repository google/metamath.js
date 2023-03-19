include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cfn.mm"
include "reprval.mm"
include "wcel.mm"
include "fzofi.mm"
include "mapfi.mm"
include "sylancl.mm"
include "rabfi.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem reprfi
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let vm: setvar m
  let va: setvar a
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume reprfi.1: |- ( ph -> A e. Fin )


  assert |- ( ph -> ( A ( repr ` S ) M ) e. Fin )

  proof
    wph
    cA
    cM
    cS
    crepr
    cfv
    co
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
    cfn
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
    wph
    @2
    cfn
    wcel
    #
    @3
    cfn
    wcel
    wph
    cA
    cfn
    wcel
    @0
    cfn
    wcel
    @4
    reprfi.1
    cc0
    cS
    fzofi
    cA
    @0
    mapfi
    sylancl
    @1
    vc
    @2
    rabfi
    syl
    eqeltrd
end
