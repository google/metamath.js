include "cfusgr.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cclwwlknon.mm"
include "ciun.mm"
include "csu.mm"
include "cusgr.mm"
include "wceq.mm"
include "fusgrusgr.mm"
include "adantr.mm"
include "clwwlknun.mm"
include "syl.mm"
include "fveq2d.mm"
include "cfn.mm"
include "fusgrvtxfi.mm"
include "clwwlknonfin.mm"
include "wdisj.mm"
include "clwwlknondisj.mm"
include "a1i.mm"
include "hashiun.mm"
include "eqtrd.mm"

theorem numclwwlk4
  let vx: setvar x
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let cX: class X
  assume numclwwlk3.v: |- V = ( Vtx ` G )

  disjoint G x
  disjoint N x
  disjoint V x
  disjoint G n
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint K w
  disjoint N n
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  assert |- ( ( G e. FinUSGraph /\ N e. NN ) -> ( # ` ( N ClWWalksN G ) ) = sum_ x e. V ( # ` ( x ( ClWWalksNOn ` G ) N ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cN
    cG
    cclwwlkn
    co
    #
    chash
    cfv
    vx
    cV
    vx
    cv
    #
    cN
    cG
    cclwwlknon
    cfv
    co
    #
    ciun
    #
    chash
    cfv
    cV
    @5
    chash
    cfv
    vx
    csu
    @2
    @3
    @6
    chash
    @2
    cG
    cusgr
    wcel
    #
    @3
    @6
    wceq
    @0
    @7
    @1
    cG
    fusgrusgr
    adantr
    vx
    cG
    cN
    cV
    numclwwlk3.v
    clwwlknun
    syl
    fveq2d
    @2
    vx
    cV
    @5
    @0
    cV
    cfn
    wcel
    #
    @1
    cG
    cV
    numclwwlk3.v
    fusgrvtxfi
    #
    adantr
    @2
    @5
    cfn
    wcel
    #
    @4
    cV
    wcel
    @0
    @10
    @1
    @0
    @8
    @10
    @9
    cG
    cN
    cV
    @4
    numclwwlk3.v
    clwwlknonfin
    syl
    adantr
    adantr
    vx
    cV
    @5
    wdisj
    @2
    vx
    cG
    cN
    cV
    clwwlknondisj
    a1i
    hashiun
    eqtrd
end
