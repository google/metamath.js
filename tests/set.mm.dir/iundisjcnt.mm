include "cn.mm"
include "wceq.mm"
include "ciun.mm"
include "c1.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "cdif.mm"
include "wa.mm"
include "nfcv.mm"
include "iundisjf.mm"
include "simpr.mm"
include "iuneq1d.mm"
include "3eqtr4a.mm"
include "iundisjfi.mm"
include "mpjaodan.mm"

theorem iundisjcnt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cN: class N
  assume iundisjcnt.0: |- F/_ n B
  assume iundisjcnt.1: |- ( n = k -> A = B )
  assume iundisjcnt.2: |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) )

  disjoint A k
  disjoint k n
  disjoint M k
  disjoint M n
  disjoint N k
  disjoint N n
  assert |- ( ph -> U_ n e. N A = U_ n e. N ( A \ U_ k e. ( 1 ..^ n ) B ) )

  proof
    wph
    cN
    cn
    wceq
    #
    vn
    cN
    cA
    ciun
    #
    vn
    cN
    cA
    vk
    c1
    vn
    cv
    cfzo
    co
    cB
    ciun
    cdif
    #
    ciun
    #
    wceq
    cN
    c1
    cM
    cfzo
    co
    #
    wceq
    #
    wph
    @0
    wa
    #
    vn
    cn
    cA
    ciun
    vn
    cn
    @2
    ciun
    @1
    @3
    cA
    cB
    vk
    vn
    vk
    cA
    nfcv
    iundisjcnt.0
    iundisjcnt.1
    iundisjf
    @6
    vn
    cN
    cn
    cA
    wph
    @0
    simpr
    #
    iuneq1d
    @6
    vn
    cN
    cn
    @2
    @7
    iuneq1d
    3eqtr4a
    wph
    @5
    wa
    #
    vn
    @4
    cA
    ciun
    vn
    @4
    @2
    ciun
    @1
    @3
    cA
    cB
    vk
    vn
    cM
    iundisjcnt.0
    iundisjcnt.1
    iundisjfi
    @8
    vn
    cN
    @4
    cA
    wph
    @5
    simpr
    #
    iuneq1d
    @8
    vn
    cN
    @4
    @2
    @9
    iuneq1d
    3eqtr4a
    iundisjcnt.2
    mpjaodan
end
