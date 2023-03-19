include "cc.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cprod.mm"
include "cmpt.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "eqid.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "fprodaddrecnncnvlem.mm"

theorem fprodaddrecnncnv
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cX: class X
  let vx: setvar x
  let vm: setvar m
  assume fprodaddrecnncnv.1: |- F/ k ph
  assume fprodaddrecnncnv.2: |- ( ph -> X e. Fin )
  assume fprodaddrecnncnv.3: |- ( ( ph /\ k e. X ) -> A e. CC )
  assume fprodaddrecnncnv.4: |- S = ( n e. NN |-> prod_ k e. X ( A + ( 1 / n ) ) )

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
    caddc
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
    fprodaddrecnncnv.1
    fprodaddrecnncnv.2
    fprodaddrecnncnv.3
    fprodaddrecnncnv.4
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
    fprodaddrecnncnvlem
end
