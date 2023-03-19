include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "crab.mm"
include "wa.mm"
include "crepr.mm"
include "reprval.mm"
include "eleqtrd.mm"
include "fveq1.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"

theorem reprsum
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

  disjoint C a
  disjoint S a
  disjoint C c
  disjoint a c
  disjoint A b
  disjoint A c
  disjoint A m
  disjoint b c
  disjoint b m
  disjoint c m
  disjoint M b
  disjoint M c
  disjoint M m
  disjoint S b
  disjoint S c
  disjoint S m
  disjoint S s
  disjoint a b
  disjoint a c
  disjoint a m
  disjoint a s
  disjoint b s
  disjoint c s
  disjoint m s
  disjoint b ph
  disjoint c ph
  disjoint m ph
  disjoint ph s
  assert |- ( ph -> sum_ a e. ( 0 ..^ S ) ( C ` a ) = M )

  proof
    wph
    cC
    cA
    cc0
    cS
    cfzo
    co
    #
    cmap
    co
    #
    wcel
    #
    @0
    va
    cv
    #
    cC
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    wph
    cC
    @0
    @3
    vc
    cv
    #
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    vc
    @1
    crab
    #
    wcel
    @2
    @6
    wa
    wph
    cC
    cA
    cM
    cS
    crepr
    cfv
    co
    @11
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
    @10
    @6
    vc
    cC
    @1
    @7
    cC
    wceq
    #
    @9
    @5
    cM
    @12
    @0
    @8
    @4
    va
    @3
    @7
    cC
    fveq1
    sumeq2sdv
    eqeq1d
    elrab
    sylib
    simprd
end
