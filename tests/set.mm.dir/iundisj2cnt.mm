include "cn.mm"
include "wceq.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wo.mm"
include "cv.mm"
include "ciun.mm"
include "cdif.mm"
include "wdisj.mm"
include "nfcv.mm"
include "iundisj2f.mm"
include "disjeq1.mm"
include "mpbiri.mm"
include "iundisj2fi.mm"
include "jaoi.mm"
include "syl.mm"

theorem iundisj2cnt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cN: class N
  assume iundisj2cnt.0: |- F/_ n B
  assume iundisj2cnt.1: |- ( n = k -> A = B )
  assume iundisj2cnt.2: |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) )

  disjoint k n
  disjoint M k
  disjoint M n
  disjoint A k
  disjoint N n
  assert |- ( ph -> Disj_ n e. N ( A \ U_ k e. ( 1 ..^ n ) B ) )

  proof
    wph
    cN
    cn
    wceq
    #
    cN
    c1
    cM
    cfzo
    co
    #
    wceq
    #
    wo
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
    wdisj
    #
    iundisj2cnt.2
    @0
    @4
    @2
    @0
    @4
    vn
    cn
    @3
    wdisj
    cA
    cB
    vk
    vn
    vk
    cA
    nfcv
    iundisj2cnt.0
    iundisj2cnt.1
    iundisj2f
    vn
    cN
    cn
    @3
    disjeq1
    mpbiri
    @2
    @4
    vn
    @1
    @3
    wdisj
    cA
    cB
    vk
    vn
    cM
    iundisj2cnt.0
    iundisj2cnt.1
    iundisj2fi
    vn
    cN
    @1
    @3
    disjeq1
    mpbiri
    jaoi
    syl
end
