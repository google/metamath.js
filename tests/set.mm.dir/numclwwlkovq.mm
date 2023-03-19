include "cn.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "clsw.mm"
include "wne.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "oveq1.mm"
include "adantl.mm"
include "wb.mm"
include "eqeq2.mm"
include "neeq2.mm"
include "anbi12d.mm"
include "adantr.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"

theorem numclwwlkovq
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V v
  disjoint X n
  disjoint X v
  disjoint X w
  assert |- ( ( X e. V /\ N e. NN ) -> ( X Q N ) = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = X /\ ( lastS ` w ) =/= X ) } )

  proof
    vv
    vn
    cX
    cN
    cV
    cn
    cc0
    vw
    cv
    #
    cfv
    #
    vv
    cv
    #
    wceq
    #
    @0
    clsw
    cfv
    #
    @2
    wne
    #
    wa
    #
    vw
    vn
    cv
    #
    cG
    cwwlksn
    co
    #
    crab
    @1
    cX
    wceq
    #
    @4
    cX
    wne
    #
    wa
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    cQ
    @2
    cX
    wceq
    #
    @7
    cN
    wceq
    #
    wa
    @6
    @11
    vw
    @8
    @12
    @14
    @8
    @12
    wceq
    @13
    @7
    cN
    cG
    cwwlksn
    oveq1
    adantl
    @13
    @6
    @11
    wb
    @14
    @13
    @3
    @9
    @5
    @10
    @2
    cX
    @1
    eqeq2
    @2
    cX
    @4
    neeq2
    anbi12d
    adantr
    rabeqbidv
    numclwwlk.q
    @11
    vw
    @12
    cN
    cG
    cwwlksn
    ovex
    rabex
    ovmpt2a
end
