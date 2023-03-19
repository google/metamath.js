include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cword.mm"
include "csb.mm"
include "w3a.mm"
include "crab.mm"
include "cmpt2.mm"
include "wa.mm"
include "wceq.mm"
include "csbwrdg.mm"
include "eqcomd.mm"
include "adantr.mm"
include "rabeq.mm"
include "syl.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"
include "wrdexg.mm"
include "eqeltrd.mm"
include "elovmpt2rab1.mm"
include "wb.mm"
include "eleq2d.mm"
include "id.mm"
include "3expia.mm"
include "sylbid.mm"
include "3impia.mm"

theorem elovmpt2wrd
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cO: class O
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  assume elovmpt2wrd.o: |- O = ( v e. _V , y e. _V |-> { z e. Word v | ph } )

  disjoint V v
  disjoint V y
  disjoint V z
  disjoint v y
  disjoint v z
  disjoint y z
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint Z z
  disjoint V x
  disjoint v x
  disjoint x y
  disjoint x z
  assert |- ( Z e. ( V O Y ) -> ( V e. _V /\ Y e. _V /\ Z e. Word V ) )

  proof
    cZ
    cV
    cY
    cO
    co
    wcel
    cV
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    cZ
    vx
    cV
    vx
    cv
    cword
    #
    csb
    #
    wcel
    #
    w3a
    @0
    @1
    cZ
    cV
    cword
    #
    wcel
    #
    w3a
    #
    wph
    vv
    vy
    vz
    vx
    @2
    cO
    cV
    cY
    cZ
    cO
    vv
    vy
    cvv
    cvv
    wph
    vz
    vv
    cv
    #
    cword
    #
    crab
    #
    cmpt2
    vv
    vy
    cvv
    cvv
    wph
    vz
    vx
    @8
    @2
    csb
    #
    crab
    #
    cmpt2
    elovmpt2wrd.o
    vv
    vy
    cvv
    cvv
    @10
    @12
    @8
    cvv
    wcel
    #
    vy
    cv
    cvv
    wcel
    #
    wa
    @9
    @11
    wceq
    #
    @10
    @12
    wceq
    @13
    @15
    @14
    @13
    @11
    @9
    vx
    @8
    cvv
    csbwrdg
    eqcomd
    adantr
    wph
    vz
    @9
    @11
    rabeq
    syl
    mpt2eq3ia
    eqtri
    @0
    @3
    cvv
    wcel
    @1
    @0
    @3
    @5
    cvv
    vx
    cV
    cvv
    csbwrdg
    #
    cV
    cvv
    wrdexg
    eqeltrd
    adantr
    elovmpt2rab1
    @0
    @1
    @4
    @7
    @0
    @1
    wa
    @4
    @6
    @7
    @0
    @4
    @6
    wb
    @1
    @0
    @3
    @5
    cZ
    @16
    eleq2d
    adantr
    @0
    @1
    @6
    @7
    @7
    id
    3expia
    sylbid
    3impia
    syl
end
