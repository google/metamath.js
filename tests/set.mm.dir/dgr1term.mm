include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "cdgr.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ccoe.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "wi.mm"
include "coe1termlem.mm"
include "simprd.mm"
include "3impia.mm"
include "3com23.mm"

theorem dgr1term
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  assume coe1term.1: |- F = ( z e. CC |-> ( A x. ( z ^ N ) ) )

  disjoint A z
  disjoint N z
  disjoint k n
  disjoint k z
  disjoint A k
  disjoint n z
  disjoint A n
  disjoint M n
  disjoint N k
  disjoint N n
  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. NN0 ) -> ( deg ` F ) = N )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cc0
    wne
    #
    cF
    cdgr
    cfv
    cN
    wceq
    #
    @0
    @1
    @2
    @3
    @0
    @1
    wa
    cF
    ccoe
    cfv
    vn
    cn0
    vn
    cv
    cN
    wceq
    cA
    cc0
    cif
    cmpt
    wceq
    @2
    @3
    wi
    vz
    cA
    vn
    cF
    cN
    coe1term.1
    coe1termlem
    simprd
    3impia
    3com23
end
