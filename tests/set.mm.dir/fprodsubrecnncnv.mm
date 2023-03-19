include "cc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cprod.mm"
include "cmpt.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "eqid.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "fprodsubrecnncnvlem.mm"

theorem fprodsubrecnncnv
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cX: class X
  let vx: setvar x
  let vm: setvar m
  assume fprodsubrecnncnv.1: |- F/ k ph
  assume fprodsubrecnncnv.2: |- ( ph -> X e. Fin )
  assume fprodsubrecnncnv.3: |- ( ( ph /\ k e. X ) -> A e. CC )
  assume fprodsubrecnncnv.4: |- S = ( n e. NN |-> prod_ k e. X ( A - ( 1 / n ) ) )

  disjoint A n
  disjoint X k
  disjoint X n
  disjoint k n
  disjoint n ph
  disjoint A x
  disjoint n x
  disjoint X x
  disjoint k x
  disjoint m n
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S ~~> prod_ k e. X A )

  proof
    wph
    vx
    cX
    cA
    cS
    vk
    vn
    vx
    cc
    cX
    cA
    vx
    cv
    cmin
    co
    vk
    cprod
    cmpt
    #
    vm
    cn
    c1
    vm
    cv
    #
    cdiv
    co
    #
    cmpt
    fprodsubrecnncnv.1
    fprodsubrecnncnv.2
    fprodsubrecnncnv.3
    fprodsubrecnncnv.4
    @0
    eqid
    vm
    vn
    cn
    @2
    c1
    vn
    cv
    #
    cdiv
    co
    @1
    @3
    c1
    cdiv
    oveq2
    cbvmptv
    fprodsubrecnncnvlem
end
