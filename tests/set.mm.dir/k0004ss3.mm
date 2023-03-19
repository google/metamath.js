include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cmap.mm"
include "cehl.mm"
include "cbs.mm"
include "k0004ss1.mm"
include "wceq.mm"
include "peano2nn0.mm"
include "eqid.mm"
include "ehlbase.mm"
include "syl.mm"
include "sseqtrd.mm"

theorem k0004ss3
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vv: setvar v
  assume k0004.a: |- A = ( n e. NN0 |-> { t e. ( ( 0 [,] 1 ) ^m ( 1 ... ( n + 1 ) ) ) | sum_ k e. ( 1 ... ( n + 1 ) ) ( t ` k ) = 1 } )

  disjoint k n
  disjoint n t
  disjoint N k
  disjoint N t
  disjoint N n
  disjoint N v
  assert |- ( N e. NN0 -> ( A ` N ) C_ ( Base ` ( EEhil ` ( N + 1 ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cA
    cfv
    cr
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    cmap
    co
    #
    @1
    cehl
    cfv
    #
    cbs
    cfv
    #
    vt
    cA
    vk
    vn
    cN
    k0004.a
    k0004ss1
    @0
    @1
    cn0
    wcel
    @2
    @4
    wceq
    cN
    peano2nn0
    @3
    @1
    @3
    eqid
    ehlbase
    syl
    sseqtrd
end
