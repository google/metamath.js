include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "fsum0diaglem.mm"
include "impbii.mm"
include "a1i.mm"
include "fprodcom2.mm"

theorem fprod0diag
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  assume fprod0diag.1: |- ( ( ph /\ ( j e. ( 0 ... N ) /\ k e. ( 0 ... ( N - j ) ) ) ) -> A e. CC )

  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint N j
  disjoint N k
  assert |- ( ph -> prod_ j e. ( 0 ... N ) prod_ k e. ( 0 ... ( N - j ) ) A = prod_ k e. ( 0 ... N ) prod_ j e. ( 0 ... ( N - k ) ) A )

  proof
    wph
    cc0
    cN
    cfz
    co
    #
    cc0
    cN
    vj
    cv
    #
    cmin
    co
    #
    cfz
    co
    #
    @0
    cc0
    cN
    vk
    cv
    #
    cmin
    co
    cfz
    co
    #
    vj
    vk
    cA
    wph
    cc0
    cN
    fzfid
    #
    @6
    wph
    @1
    @0
    wcel
    #
    wa
    cc0
    @2
    fzfid
    @7
    @4
    @3
    wcel
    wa
    #
    @4
    @0
    wcel
    @1
    @5
    wcel
    wa
    #
    wb
    wph
    @8
    @9
    vj
    vk
    cN
    fsum0diaglem
    vk
    vj
    cN
    fsum0diaglem
    impbii
    a1i
    fprod0diag.1
    fprodcom2
end
