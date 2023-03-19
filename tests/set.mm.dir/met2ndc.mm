include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "c2ndc.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ccl.mm"
include "wceq.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "cuni.mm"
include "eqid.mm"
include "2ndcsep.mm"
include "mopnuni.mm"
include "pweqd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "syl5ibr.mm"
include "wss.mm"
include "wi.mm"
include "elpwi.mm"
include "met2ndci.mm"
include "3exp2.mm"
include "imp4a.mm"
include "syl5.mm"
include "rexlimdv.mm"
include "impbid.mm"

theorem met2ndc
  let vx: setvar x
  let cD: class D
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cA: class A
  assume methaus.1: |- J = ( MetOpen ` D )

  disjoint D x
  disjoint J x
  disjoint X x
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d u
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint D n
  disjoint r t
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint d m
  disjoint J d
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint J n
  disjoint J r
  disjoint J t
  disjoint J u
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint A n
  disjoint A r
  disjoint A t
  disjoint A u
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint X d
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( D e. ( *Met ` X ) -> ( J e. 2ndc <-> E. x e. ~P X ( x ~<_ _om /\ ( ( cls ` J ) ` x ) = X ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    c2ndc
    wcel
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @2
    cJ
    ccl
    cfv
    cfv
    #
    cX
    wceq
    #
    wa
    #
    vx
    cX
    cpw
    #
    wrex
    #
    @1
    @8
    @0
    @3
    @4
    cJ
    cuni
    #
    wceq
    #
    wa
    #
    vx
    @9
    cpw
    #
    wrex
    vx
    cJ
    @9
    @9
    eqid
    2ndcsep
    @0
    @6
    @11
    vx
    @7
    @12
    @0
    cX
    @9
    cD
    cJ
    cX
    methaus.1
    mopnuni
    #
    pweqd
    @0
    @5
    @10
    @3
    @0
    cX
    @9
    @4
    @13
    eqeq2d
    anbi2d
    rexeqbidv
    syl5ibr
    @0
    @6
    @1
    vx
    @7
    @2
    @7
    wcel
    @2
    cX
    wss
    #
    @0
    @6
    @1
    wi
    @2
    cX
    elpwi
    @0
    @14
    @3
    @5
    @1
    @0
    @14
    @3
    @5
    @1
    @2
    cD
    cJ
    cX
    methaus.1
    met2ndci
    3exp2
    imp4a
    syl5
    rexlimdv
    impbid
end
