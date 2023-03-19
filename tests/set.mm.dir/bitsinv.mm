include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "sumeq1.mm"
include "cbits.mm"
include "cres.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wceq.mm"
include "bitsf1ocnv.mm"
include "simpri.mm"
include "eqtri.mm"
include "sumex.mm"
include "fvmpt.mm"

theorem bitsinv
  let cA: class A
  let vk: setvar k
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume bitsinv.k: |- K = `' ( bits |` NN0 )

  disjoint A k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint k y
  disjoint N k
  disjoint n y
  disjoint N n
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( A e. ( ~P NN0 i^i Fin ) -> ( K ` A ) = sum_ k e. A ( 2 ^ k ) )

  proof
    vx
    cA
    vx
    cv
    #
    c2
    vk
    cv
    cexp
    co
    #
    vk
    csu
    #
    cA
    @1
    vk
    csu
    cn0
    cpw
    cfn
    cin
    #
    cK
    @0
    cA
    @1
    vk
    sumeq1
    cK
    cbits
    cn0
    cres
    #
    ccnv
    #
    vx
    @3
    @2
    cmpt
    #
    bitsinv.k
    cn0
    @3
    @4
    wf1o
    @5
    @6
    wceq
    vx
    vk
    bitsf1ocnv
    simpri
    eqtri
    cA
    @1
    vk
    sumex
    fvmpt
end
