include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "plybss.mm"
include "cab.mm"
include "plyval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wi.mm"
include "wa.mm"
include "id.mm"
include "cnex.mm"
include "mptex.mm"
include "syl6eqel.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem elply
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let va: setvar a
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cT: class T

  disjoint a k
  disjoint a n
  disjoint a z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint S a
  disjoint S k
  disjoint S n
  disjoint S z
  disjoint F a
  disjoint F n
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A z
  disjoint N a
  disjoint N k
  disjoint N n
  disjoint N z
  disjoint a f
  disjoint a x
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f z
  disjoint S f
  disjoint k x
  disjoint n x
  disjoint x z
  disjoint S x
  disjoint T a
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T z
  disjoint F f
  assert |- ( F e. ( Poly ` S ) <-> ( S C_ CC /\ E. n e. NN0 E. a e. ( ( S u. { 0 } ) ^m NN0 ) F = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cS
    cc
    wss
    #
    cF
    vz
    cc
    cc0
    vn
    cv
    #
    cfz
    co
    vk
    cv
    #
    va
    cv
    #
    cfv
    vz
    cv
    @4
    cexp
    co
    cmul
    co
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    va
    cS
    cc0
    csn
    cun
    cn0
    cmap
    co
    #
    wrex
    vn
    cn0
    wrex
    #
    cS
    cF
    plybss
    @2
    @1
    cF
    vf
    cv
    #
    @7
    wceq
    #
    va
    @9
    wrex
    vn
    cn0
    wrex
    #
    vf
    cab
    #
    wcel
    @10
    @2
    @0
    @14
    cF
    vz
    cS
    vf
    vk
    vn
    va
    plyval
    eleq2d
    @13
    @10
    vf
    cF
    @8
    cF
    cvv
    wcel
    #
    vn
    va
    cn0
    @9
    @8
    @15
    wi
    @3
    cn0
    wcel
    @5
    @9
    wcel
    wa
    @8
    cF
    @7
    cvv
    @8
    id
    vz
    cc
    @6
    cnex
    mptex
    syl6eqel
    a1i
    rexlimivv
    @11
    cF
    wceq
    @12
    @8
    vn
    va
    cn0
    @9
    @11
    cF
    @7
    eqeq1
    2rexbidv
    elab3
    syl6bb
    biadan2
end
