include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "crepr.mm"
include "cfv.mm"
include "chash.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cn.mm"
include "cind.mm"
include "cprod.mm"
include "csu.mm"
include "nn0zd.mm"
include "fzfid.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "a1i.mm"
include "hashreprin.mm"
include "reprinfz1.mm"
include "fveq2d.mm"
include "reprfz1.mm"
include "sumeq1d.mm"
include "3eqtr4d.mm"

theorem hashrepr
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let va: setvar a
  let vc: setvar c
  assume hashrepr.a: |- ( ph -> A C_ NN )
  assume hashrepr.m: |- ( ph -> M e. NN0 )
  assume hashrepr.s: |- ( ph -> S e. NN0 )

  disjoint A a
  disjoint A c
  disjoint a c
  disjoint M a
  disjoint M c
  disjoint S a
  disjoint S c
  disjoint a ph
  disjoint c ph
  assert |- ( ph -> ( # ` ( A ( repr ` S ) M ) ) = sum_ c e. ( NN ( repr ` S ) M ) prod_ a e. ( 0 ..^ S ) ( ( ( _Ind ` NN ) ` A ) ` ( c ` a ) ) )

  proof
    wph
    cA
    c1
    cM
    cfz
    co
    #
    cin
    cM
    cS
    crepr
    cfv
    #
    co
    #
    chash
    cfv
    @0
    cM
    @1
    co
    #
    cc0
    cS
    cfzo
    co
    va
    cv
    vc
    cv
    cfv
    cA
    cn
    cind
    cfv
    cfv
    cfv
    va
    cprod
    #
    vc
    csu
    cA
    cM
    @1
    co
    #
    chash
    cfv
    cn
    cM
    @1
    co
    #
    @4
    vc
    csu
    wph
    cA
    @0
    cS
    cM
    va
    vc
    hashrepr.a
    wph
    cM
    hashrepr.m
    nn0zd
    hashrepr.s
    wph
    c1
    cM
    fzfid
    @0
    cn
    wss
    wph
    cM
    fz1ssnn
    a1i
    hashreprin
    wph
    @5
    @2
    chash
    wph
    cA
    cS
    cM
    hashrepr.m
    hashrepr.s
    hashrepr.a
    reprinfz1
    fveq2d
    wph
    @6
    @3
    @4
    vc
    wph
    cS
    cM
    hashrepr.m
    hashrepr.s
    reprfz1
    sumeq1d
    3eqtr4d
end
