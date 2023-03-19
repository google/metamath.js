include "cq.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cr.mm"
include "cdom.mm"
include "wbr.mm"
include "ovex.mm"
include "cv.mm"
include "cfv.mm"
include "rpnnen1lem1.mm"
include "wa.mm"
include "wceq.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "rneq.mm"
include "supeq1d.mm"
include "rpnnen1lem5.mm"
include "fveq2.mm"
include "rneqd.mm"
include "id.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "impbid1.mm"
include "dom2.mm"
include "ax-mp.mm"

theorem rpnnen1lem6
  let vx: setvar x
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume rpnnen1lem.1: |- T = { n e. ZZ | ( n / k ) < x }
  assume rpnnen1lem.2: |- F = ( x e. RR |-> ( k e. NN |-> ( sup ( T , RR , < ) / k ) ) )
  assume rpnnen1lem.n: |- NN e. _V
  assume rpnnen1lem.q: |- QQ e. _V

  disjoint F k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint T n
  disjoint F y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint T y
  assert |- RR ~<_ ( QQ ^m NN )

  proof
    cq
    cn
    cmap
    co
    #
    cvv
    wcel
    cr
    @0
    cdom
    wbr
    cq
    cn
    cmap
    ovex
    vx
    vy
    cr
    @0
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cvv
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem1
    @1
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    wa
    #
    @2
    @4
    wceq
    #
    @1
    @3
    wceq
    #
    @8
    @2
    crn
    #
    cr
    clt
    csup
    #
    @4
    crn
    #
    cr
    clt
    csup
    #
    wceq
    @7
    @9
    @8
    cr
    @10
    @12
    clt
    @2
    @4
    rneq
    supeq1d
    @5
    @6
    @11
    @1
    @13
    @3
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem5
    #
    @11
    @1
    wceq
    @13
    @3
    wceq
    vx
    @3
    cr
    @9
    @11
    @13
    @1
    @3
    @9
    cr
    @10
    @12
    clt
    @9
    @2
    @4
    @1
    @3
    cF
    fveq2
    #
    rneqd
    supeq1d
    @9
    id
    eqeq12d
    @14
    vtoclga
    eqeqan12d
    syl5ib
    @15
    impbid1
    dom2
    ax-mp
end
