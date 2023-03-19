include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "fveq2.mm"
include "cfn.mm"
include "wcel.mm"
include "fzofi.mm"
include "a1i.mm"
include "reprsum.mm"
include "wa.mm"
include "cn.mm"
include "wss.mm"
include "adantr.mm"
include "reprf.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "nnrpd.mm"
include "fsumub.mm"

theorem reprle
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let cM: class M
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let vm: setvar m
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume reprf.c: |- ( ph -> C e. ( A ( repr ` S ) M ) )
  assume reprle.x: |- ( ph -> X e. ( 0 ..^ S ) )


  assert |- ( ph -> ( C ` X ) <_ M )

  proof
    wph
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    #
    cC
    cfv
    #
    cM
    cX
    cC
    cfv
    va
    cX
    @1
    cX
    cC
    fveq2
    @0
    cfn
    wcel
    wph
    cc0
    cS
    fzofi
    a1i
    wph
    cA
    cC
    cS
    cM
    va
    reprval.a
    reprval.m
    reprval.s
    reprf.c
    reprsum
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    @4
    cA
    cn
    @2
    wph
    cA
    cn
    wss
    @3
    reprval.a
    adantr
    wph
    @0
    cA
    @1
    cC
    wph
    cA
    cC
    cS
    cM
    reprval.a
    reprval.m
    reprval.s
    reprf.c
    reprf
    ffvelrnda
    sseldd
    nnrpd
    reprle.x
    fsumub
end
