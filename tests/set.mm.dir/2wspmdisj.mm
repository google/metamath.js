include "cv.mm"
include "cfv.mm"
include "wdisj.mm"
include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "orc.mm"
include "a1d.mm"
include "wn.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "co.mm"
include "c1.mm"
include "wb.mm"
include "fusgreg2wsplem.mm"
include "adantl.mm"
include "adantr.mm"
include "eqtr2.mm"
include "expcom.mm"
include "com12.mm"
include "syl6bi.mm"
include "imp.mm"
include "sylbid.mm"
include "con3d.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "disj.mm"
include "sylibr.mm"
include "olcd.mm"
include "pm2.61i.mm"
include "rgen2a.mm"
include "fveq2.mm"
include "disjor.mm"
include "mpbir.mm"

theorem 2wspmdisj
  let vx: setvar x
  let vw: setvar w
  let cG: class G
  let cM: class M
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cN: class N
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vc: setvar c
  let vd: setvar d
  let vv: setvar v
  let cK: class K
  let vt: setvar t
  assume frgrhash2wsp.v: |- V = ( Vtx ` G )
  assume fusgreg2wsp.m: |- M = ( a e. V |-> { w e. ( 2 WSPathsN G ) | ( w ` 1 ) = a } )

  disjoint G a
  disjoint V a
  disjoint G w
  disjoint a w
  disjoint G x
  disjoint V x
  disjoint a x
  disjoint w x
  disjoint M x
  disjoint V w
  disjoint G b
  disjoint a b
  disjoint V b
  disjoint N a
  disjoint N w
  disjoint G m
  disjoint G y
  disjoint G z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G p
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint M z
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint V m
  disjoint V y
  disjoint V z
  disjoint w z
  disjoint G c
  disjoint G d
  disjoint G v
  disjoint c d
  disjoint c v
  disjoint d v
  disjoint K c
  disjoint K d
  disjoint V c
  disjoint V d
  disjoint a v
  disjoint v w
  disjoint a p
  disjoint p w
  disjoint M p
  disjoint V p
  disjoint a y
  disjoint w y
  disjoint M t
  disjoint M y
  disjoint t x
  disjoint t y
  disjoint V t
  disjoint t w
  assert |- Disj_ x e. V ( M ` x )

  proof
    vx
    cV
    vx
    cv
    #
    cM
    cfv
    #
    wdisj
    vx
    vy
    weq
    #
    @1
    vy
    cv
    #
    cM
    cfv
    #
    cin
    c0
    wceq
    #
    wo
    #
    vy
    cV
    wral
    vx
    cV
    wral
    @6
    vx
    vy
    cV
    @2
    @0
    cV
    wcel
    #
    @3
    cV
    wcel
    #
    wa
    #
    @6
    wi
    @2
    @6
    @9
    @2
    @5
    orc
    a1d
    @9
    @2
    wn
    #
    @6
    @9
    @10
    wa
    #
    @5
    @2
    @11
    vt
    cv
    #
    @4
    wcel
    #
    wn
    #
    vt
    @1
    wral
    @5
    @11
    @14
    vt
    @1
    @9
    @12
    @1
    wcel
    #
    @10
    @14
    @9
    @15
    wa
    #
    @13
    @2
    @16
    @13
    @12
    c2
    cG
    cwwspthsn
    co
    wcel
    #
    c1
    @12
    cfv
    #
    @3
    wceq
    #
    wa
    #
    @2
    @9
    @13
    @20
    wb
    #
    @15
    @8
    @21
    @7
    vw
    cG
    cM
    @3
    cV
    vt
    va
    frgrhash2wsp.v
    fusgreg2wsp.m
    fusgreg2wsplem
    adantl
    adantr
    @9
    @15
    @20
    @2
    wi
    #
    @7
    @15
    @22
    wi
    @8
    @7
    @15
    @17
    @18
    @0
    wceq
    #
    wa
    @22
    vw
    cG
    cM
    @0
    cV
    vt
    va
    frgrhash2wsp.v
    fusgreg2wsp.m
    fusgreg2wsplem
    @23
    @22
    @17
    @20
    @23
    @2
    @19
    @23
    @2
    wi
    @17
    @23
    @19
    @2
    @18
    @0
    @3
    eqtr2
    expcom
    adantl
    com12
    adantl
    syl6bi
    adantr
    imp
    sylbid
    con3d
    impancom
    ralrimiv
    vt
    @1
    @4
    disj
    sylibr
    olcd
    expcom
    pm2.61i
    rgen2a
    cV
    @1
    @4
    vx
    vy
    @0
    @3
    cM
    fveq2
    disjor
    mpbir
end
