include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "wi.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "breq1.mm"
include "rabbidv.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "1z.mm"
include "elimel.mm"
include "peano5uzi.mm"
include "dedth.mm"

theorem peano5uzti
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vn: setvar n

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint N k
  disjoint N x
  disjoint k n
  disjoint n x
  disjoint A n
  disjoint N n
  assert |- ( N e. ZZ -> ( ( N e. A /\ A. x e. A ( x + 1 ) e. A ) -> { k e. ZZ | N <_ k } C_ A ) )

  proof
    cN
    cz
    wcel
    #
    cN
    cA
    wcel
    #
    vx
    cv
    c1
    caddc
    co
    cA
    wcel
    vx
    cA
    wral
    #
    wa
    #
    cN
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cz
    crab
    #
    cA
    wss
    #
    wi
    @0
    cN
    c1
    cif
    #
    cA
    wcel
    #
    @2
    wa
    #
    @8
    @4
    cle
    wbr
    #
    vk
    cz
    crab
    #
    cA
    wss
    #
    wi
    cN
    c1
    cN
    @8
    wceq
    #
    @3
    @10
    @7
    @13
    @14
    @1
    @9
    @2
    cN
    @8
    cA
    eleq1
    anbi1d
    @14
    @6
    @12
    cA
    @14
    @5
    @11
    vk
    cz
    cN
    @8
    @4
    cle
    breq1
    rabbidv
    sseq1d
    imbi12d
    vx
    cA
    vk
    @8
    cN
    c1
    cz
    1z
    elimel
    peano5uzi
    dedth
end
