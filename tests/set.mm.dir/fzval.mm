include "cz.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "cfz.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "breq2.mm"
include "anbi2d.mm"
include "df-fz.mm"
include "zex.mm"
include "rabex.mm"
include "ovmpt2.mm"

theorem fzval
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n

  disjoint M k
  disjoint N k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint M m
  disjoint M n
  disjoint N m
  disjoint N n
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M ... N ) = { k e. ZZ | ( M <_ k /\ k <_ N ) } )

  proof
    vm
    vn
    cM
    cN
    cz
    cz
    vm
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    @1
    vn
    cv
    #
    cle
    wbr
    #
    wa
    #
    vk
    cz
    crab
    cM
    @1
    cle
    wbr
    #
    @1
    cN
    cle
    wbr
    #
    wa
    #
    vk
    cz
    crab
    cfz
    @6
    @4
    wa
    #
    vk
    cz
    crab
    @0
    cM
    wceq
    #
    @5
    @9
    vk
    cz
    @10
    @2
    @6
    @4
    @0
    cM
    @1
    cle
    breq1
    anbi1d
    rabbidv
    @3
    cN
    wceq
    #
    @9
    @8
    vk
    cz
    @11
    @4
    @7
    @6
    @3
    cN
    @1
    cle
    breq2
    anbi2d
    rabbidv
    vk
    vm
    vn
    df-fz
    @8
    vk
    cz
    zex
    rabex
    ovmpt2
end
