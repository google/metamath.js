include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "caddc.mm"
include "cfz.mm"
include "cmap.mm"
include "cr.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "crab.mm"
include "k0004val.mm"
include "simp2.mm"
include "rabssdv.mm"
include "eqsstrd.mm"
include "cvv.mm"
include "wss.mm"
include "reex.mm"
include "unitssre.mm"
include "mapss.mm"
include "mp2an.mm"
include "syl6ss.mm"

theorem k0004ss1
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
  assert |- ( N e. NN0 -> ( A ` N ) C_ ( RR ^m ( 1 ... ( N + 1 ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cA
    cfv
    #
    cc0
    c1
    cicc
    co
    #
    c1
    cN
    c1
    caddc
    co
    cfz
    co
    #
    cmap
    co
    #
    cr
    @3
    cmap
    co
    #
    @0
    @1
    @3
    vk
    cv
    vt
    cv
    #
    cfv
    vk
    csu
    c1
    wceq
    #
    vt
    @4
    crab
    @4
    vt
    cA
    vk
    vn
    cN
    k0004.a
    k0004val
    @0
    @7
    vt
    @4
    @4
    @0
    @6
    @4
    wcel
    @7
    simp2
    rabssdv
    eqsstrd
    cr
    cvv
    wcel
    @2
    cr
    wss
    @4
    @5
    wss
    reex
    unitssre
    @2
    cr
    @3
    cvv
    mapss
    mp2an
    syl6ss
end
