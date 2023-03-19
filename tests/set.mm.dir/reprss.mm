include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "crepr.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "cn.mm"
include "nnex.mm"
include "a1i.mm"
include "ssexd.mm"
include "mapss.mm"
include "syl2anc.mm"
include "sselda.mm"
include "adantrr.mm"
include "rabss3d.mm"
include "sstrd.mm"
include "reprval.mm"
include "3sstr4d.mm"

theorem reprss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vc: setvar c
  let vb: setvar b
  let vm: setvar m
  let va: setvar a
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume reprss.1: |- ( ph -> B C_ A )


  assert |- ( ph -> ( B ( repr ` S ) M ) C_ ( A ( repr ` S ) M ) )

  proof
    wph
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    vc
    cv
    #
    cfv
    va
    csu
    cM
    wceq
    #
    vc
    cB
    @0
    cmap
    co
    #
    crab
    @2
    vc
    cA
    @0
    cmap
    co
    #
    crab
    cB
    cM
    cS
    crepr
    cfv
    #
    co
    cA
    cM
    @5
    co
    wph
    @2
    vc
    @3
    @4
    wph
    @1
    @3
    wcel
    @1
    @4
    wcel
    @2
    wph
    @3
    @4
    @1
    wph
    cA
    cvv
    wcel
    cB
    cA
    wss
    @3
    @4
    wss
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprval.a
    ssexd
    reprss.1
    cB
    cA
    @0
    cvv
    mapss
    syl2anc
    sselda
    adantrr
    rabss3d
    wph
    cB
    cS
    cM
    va
    vc
    wph
    cB
    cA
    cn
    reprss.1
    reprval.a
    sstrd
    reprval.m
    reprval.s
    reprval
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
    3sstr4d
end
