include "cc.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "cply.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
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
include "cab.mm"
include "cnex.mm"
include "elpw2.mm"
include "uneq1.mm"
include "oveq1d.mm"
include "rexeqdv.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "df-ply.mm"
include "nn0ex.mm"
include "ovex.mm"
include "ab2rexex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem plyval
  let vz: setvar z
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  let cA: class A
  let cN: class N
  let vx: setvar x
  let cT: class T
  let cF: class F

  disjoint a k
  disjoint a n
  disjoint a z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint a f
  disjoint S a
  disjoint f k
  disjoint f n
  disjoint f z
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S z
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A z
  disjoint N a
  disjoint N k
  disjoint N n
  disjoint N z
  disjoint a x
  disjoint f x
  disjoint k x
  disjoint n x
  disjoint x z
  disjoint S x
  disjoint T a
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T z
  disjoint F a
  disjoint F f
  disjoint F n
  assert |- ( S C_ CC -> ( Poly ` S ) = { f | E. n e. NN0 E. a e. ( ( S u. { 0 } ) ^m NN0 ) f = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) } )

  proof
    cS
    cc
    wss
    cS
    cc
    cpw
    #
    wcel
    cS
    cply
    cfv
    vf
    cv
    vz
    cc
    cc0
    vn
    cv
    cfz
    co
    vk
    cv
    #
    va
    cv
    cfv
    vz
    cv
    @1
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    #
    wceq
    #
    va
    cS
    cc0
    csn
    #
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    #
    vn
    cn0
    wrex
    #
    vf
    cab
    #
    wceq
    cS
    cc
    cnex
    elpw2
    vx
    cS
    @3
    va
    vx
    cv
    #
    @4
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    #
    vn
    cn0
    wrex
    #
    vf
    cab
    @9
    @0
    cply
    @10
    cS
    wceq
    #
    @14
    @8
    vf
    @15
    @13
    @7
    vn
    cn0
    @15
    @3
    va
    @12
    @6
    @15
    @11
    @5
    cn0
    cmap
    @10
    cS
    @4
    uneq1
    oveq1d
    rexeqdv
    rexbidv
    abbidv
    vx
    vz
    vf
    vk
    vn
    va
    df-ply
    vn
    va
    vf
    cn0
    @6
    @2
    nn0ex
    @5
    cn0
    cmap
    ovex
    ab2rexex
    fvmpt
    sylbir
end
