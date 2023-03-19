include "cfusgr.mm"
include "wcel.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wrex.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cwwlksn.mm"
include "wspthsswwlkn.mm"
include "sseli.mm"
include "midwwlks2s3.mm"
include "syl.mm"
include "a1i.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "ancom.mm"
include "rexbii.mm"
include "r19.41v.mm"
include "bitr2i.mm"
include "fusgreg2wsplem.mm"
include "bicomd.mm"
include "adantl.mm"
include "rexbidva.mm"
include "3bitrd.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem fusgreg2wsp
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
  assert |- ( G e. FinUSGraph -> ( 2 WSPathsN G ) = U_ x e. V ( M ` x ) )

  proof
    cG
    cfusgr
    wcel
    #
    vp
    c2
    cG
    cwwspthsn
    co
    #
    vx
    cV
    vx
    cv
    #
    cM
    cfv
    #
    ciun
    #
    @0
    vp
    cv
    #
    @1
    wcel
    #
    @5
    @3
    wcel
    #
    vx
    cV
    wrex
    #
    @5
    @4
    wcel
    @0
    @6
    c1
    @5
    cfv
    @2
    wceq
    #
    vx
    cV
    wrex
    #
    @6
    wa
    #
    @6
    @9
    wa
    #
    vx
    cV
    wrex
    #
    @8
    @0
    @6
    @10
    @6
    @10
    wi
    @0
    @6
    @5
    c2
    cG
    cwwlksn
    co
    #
    wcel
    @10
    @1
    @14
    @5
    cG
    c2
    wspthsswwlkn
    sseli
    cG
    cV
    @5
    vx
    frgrhash2wsp.v
    midwwlks2s3
    syl
    a1i
    pm4.71rd
    @11
    @13
    wb
    @0
    @13
    @9
    @6
    wa
    #
    vx
    cV
    wrex
    @11
    @12
    @15
    vx
    cV
    @6
    @9
    ancom
    rexbii
    @9
    @6
    vx
    cV
    r19.41v
    bitr2i
    a1i
    @0
    @12
    @7
    vx
    cV
    @2
    cV
    wcel
    #
    @12
    @7
    wb
    @0
    @16
    @7
    @12
    vw
    cG
    cM
    @2
    cV
    vp
    va
    frgrhash2wsp.v
    fusgreg2wsp.m
    fusgreg2wsplem
    bicomd
    adantl
    rexbidva
    3bitrd
    vx
    @5
    cV
    @3
    eliun
    syl6bbr
    eqrdv
end
