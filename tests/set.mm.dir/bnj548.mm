include "w-bnj15.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "cfv.mm"
include "wceq.mm"
include "bnj930.mm"
include "adantr.mm"
include "wfn.mm"
include "simp1bi.mm"
include "fndm.mm"
include "eleq2.mm"
include "biimpar.mm"
include "sylan.mm"
include "3ad2antl2.mm"
include "jca.mm"
include "cop.mm"
include "csn.mm"
include "bnj931.mm"
include "jctil.mm"
include "3anan12.mm"
include "sylibr.mm"
include "funssfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "iuneq1.mm"
include "eqcomd.mm"
include "3eqtr4g.mm"
include "3syl.mm"

theorem bnj548
  let wta: wff ta
  let wsi: wff si
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cK: class K
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj548.1: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj548.2: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj548.3: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj548.4: |- G = ( f u. { <. m , C >. } )
  assume bnj548.5: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )

  disjoint G y
  disjoint f y
  disjoint i y
  assert |- ( ( ( R _FrSe A /\ ta /\ si ) /\ i e. m ) -> B = K )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wsi
    w3a
    #
    vi
    cv
    #
    vm
    cv
    #
    wcel
    #
    wa
    #
    cG
    wfun
    #
    vf
    cv
    #
    cG
    wss
    #
    @2
    @7
    cdm
    #
    wcel
    #
    w3a
    #
    @2
    cG
    cfv
    #
    @2
    @7
    cfv
    #
    wceq
    #
    cB
    cK
    wceq
    @5
    @8
    @6
    @10
    wa
    #
    wa
    @11
    @5
    @15
    @8
    @5
    @6
    @10
    @1
    @6
    @4
    @1
    vn
    cv
    cG
    bnj548.5
    bnj930
    adantr
    wta
    @0
    @4
    @10
    wsi
    wta
    @7
    @3
    wfn
    #
    @4
    @10
    wta
    @16
    bnjwphm
    bnjwpsm
    bnj548.1
    simp1bi
    @16
    @9
    @3
    wceq
    #
    @4
    @10
    @3
    @7
    fndm
    @17
    @10
    @4
    @9
    @3
    @2
    eleq2
    biimpar
    sylan
    sylan
    3ad2antl2
    jca
    cG
    @7
    @3
    cC
    cop
    csn
    bnj548.4
    bnj931
    jctil
    @6
    @8
    @10
    3anan12
    sylibr
    @2
    cG
    @7
    funssfv
    @14
    vy
    @13
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    vy
    @12
    @18
    ciun
    #
    cB
    cK
    @14
    @20
    @19
    vy
    @12
    @13
    @18
    iuneq1
    eqcomd
    bnj548.2
    bnj548.3
    3eqtr4g
    3syl
end
