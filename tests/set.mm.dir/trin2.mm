include "ccom.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "cotr.mm"
include "brin.mm"
include "simpr.mm"
include "simpl.mm"
include "anim12d.mm"
include "com12.mm"
include "an4s.mm"
include "syl2anb.mm"
include "syl6ibr.mm"
include "alanimi.mm"
include "ex.mm"
include "sylbi.mm"
include "imp.mm"
include "sylibr.mm"

theorem trin2
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( ( R o. R ) C_ R /\ ( S o. S ) C_ S ) -> ( ( R i^i S ) o. ( R i^i S ) ) C_ ( R i^i S ) )

  proof
    cR
    cR
    ccom
    cR
    wss
    #
    cS
    cS
    ccom
    cS
    wss
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cR
    cS
    cin
    #
    wbr
    #
    @3
    vz
    cv
    #
    @4
    wbr
    #
    wa
    #
    @2
    @6
    @4
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    @4
    @4
    ccom
    @4
    wss
    @0
    @1
    @13
    @0
    @2
    @3
    cR
    wbr
    #
    @3
    @6
    cR
    wbr
    #
    wa
    #
    @2
    @6
    cR
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    @1
    @13
    wi
    vx
    vy
    vz
    cR
    cotr
    @1
    @21
    @13
    @1
    @2
    @3
    cS
    wbr
    #
    @3
    @6
    cS
    wbr
    #
    wa
    #
    @2
    @6
    cS
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    @21
    @13
    wi
    vx
    vy
    vz
    cS
    cotr
    @29
    @21
    @13
    @28
    @20
    @12
    vx
    @27
    @19
    @11
    vy
    @26
    @18
    @10
    vz
    @26
    @18
    wa
    #
    @8
    @17
    @25
    wa
    #
    @9
    @8
    @30
    @31
    @5
    @14
    @22
    wa
    @15
    @23
    wa
    @30
    @31
    wi
    #
    @7
    @2
    @3
    cR
    cS
    brin
    @3
    @6
    cR
    cS
    brin
    @14
    @15
    @22
    @23
    @32
    @30
    @16
    @24
    wa
    @31
    @30
    @16
    @17
    @24
    @25
    @26
    @18
    simpr
    @26
    @18
    simpl
    anim12d
    com12
    an4s
    syl2anb
    com12
    @2
    @6
    cR
    cS
    brin
    syl6ibr
    alanimi
    alanimi
    alanimi
    ex
    sylbi
    com12
    sylbi
    imp
    vx
    vy
    vz
    @4
    cotr
    sylibr
end
