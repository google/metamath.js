include "ce.mm"
include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "c1.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "ccom.mm"
include "cgam.mm"
include "cli.mm"
include "eqid.mm"
include "gamcvg2lem.mm"
include "gamcvg.mm"
include "eqbrtrrd.mm"

theorem gamcvg2
  let wph: wff ph
  let cA: class A
  let vm: setvar m
  let cF: class F
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cG: class G
  assume gamcvg2.f: |- F = ( m e. NN |-> ( ( ( ( m + 1 ) / m ) ^c A ) / ( ( A / m ) + 1 ) ) )
  assume gamcvg2.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )

  disjoint A m
  disjoint m ph
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint k x
  disjoint G k
  disjoint n x
  disjoint G n
  disjoint G x
  disjoint k m
  disjoint k ph
  disjoint m n
  disjoint m x
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> seq 1 ( x. , F ) ~~> ( ( _G ` A ) x. A ) )

  proof
    wph
    ce
    caddc
    vm
    cn
    cA
    vm
    cv
    #
    c1
    caddc
    co
    @0
    cdiv
    co
    clog
    cfv
    cmul
    co
    cA
    @0
    cdiv
    co
    c1
    caddc
    co
    clog
    cfv
    cmin
    co
    cmpt
    #
    c1
    cseq
    ccom
    cmul
    cF
    c1
    cseq
    cA
    cgam
    cfv
    cA
    cmul
    co
    cli
    wph
    cA
    vm
    cF
    @1
    gamcvg2.f
    gamcvg2.a
    @1
    eqid
    #
    gamcvg2lem
    wph
    cA
    vm
    @1
    @2
    gamcvg2.a
    gamcvg
    eqbrtrrd
end
