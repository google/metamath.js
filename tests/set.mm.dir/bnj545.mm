include "w-bnj15.mm"
include "w3a.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "simp1bi.mm"
include "csuc.mm"
include "anim12i.mm"
include "3adant1.mm"
include "bnj529.mm"
include "fndm.mm"
include "eleq2.mm"
include "biimparc.mm"
include "syl2anr.mm"
include "syl.mm"
include "bnj930.mm"
include "jca.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "cop.mm"
include "csn.mm"
include "bnj931.mm"
include "jctil.mm"
include "df-3an.mm"
include "3anrot.mm"
include "ancom.mm"
include "3bitr3i.mm"
include "sylibr.mm"
include "funssfv.mm"
include "simp2bi.mm"
include "3ad2ant2.mm"
include "eqtr.mm"
include "sylan2b.mm"
include "syl2anc.mm"

theorem bnj545
  let wta: wff ta
  let wsi: wff si
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwphn: wff ph"
  assume bnj545.1: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj545.2: |- D = ( _om \ { (/) } )
  assume bnj545.3: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj545.4: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj545.5: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj545.6: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )
  assume bnj545.7: |- ( ph" <-> ( G ` (/) ) = _pred ( x , A , R ) )


  assert |- ( ( R _FrSe A /\ ta /\ si ) -> ph" )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wsi
    w3a
    #
    c0
    cG
    cfv
    #
    c0
    vf
    cv
    #
    cfv
    #
    wceq
    #
    bnjwphm
    bnjwphn
    @1
    cG
    wfun
    #
    @3
    cG
    wss
    #
    c0
    @3
    cdm
    #
    wcel
    #
    w3a
    #
    @5
    @1
    @7
    @9
    @6
    wa
    #
    wa
    #
    @10
    @1
    @11
    @7
    @1
    @9
    @6
    @1
    @3
    vm
    cv
    #
    wfn
    #
    @13
    cD
    wcel
    #
    wa
    #
    @9
    wta
    wsi
    @16
    @0
    wta
    @14
    wsi
    @15
    wta
    @14
    bnjwphm
    bnjwpsm
    bnj545.4
    simp1bi
    wsi
    @15
    vn
    cv
    #
    @13
    csuc
    wceq
    vp
    cv
    #
    @13
    wcel
    bnj545.5
    simp1bi
    anim12i
    3adant1
    @15
    c0
    @13
    wcel
    #
    @8
    @13
    wceq
    #
    @9
    @14
    cD
    @13
    bnj545.2
    bnj529
    @13
    @3
    fndm
    @20
    @9
    @19
    @8
    @13
    c0
    eleq2
    biimparc
    syl2anr
    syl
    @1
    @17
    cG
    bnj545.6
    bnj930
    jca
    cG
    @3
    @13
    vy
    @18
    @3
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    cop
    csn
    bnj545.3
    bnj931
    jctil
    @9
    @6
    @7
    w3a
    @11
    @7
    wa
    @10
    @12
    @9
    @6
    @7
    df-3an
    @9
    @6
    @7
    3anrot
    @11
    @7
    ancom
    3bitr3i
    sylibr
    c0
    cG
    @3
    funssfv
    syl
    wta
    @0
    bnjwphm
    wsi
    wta
    @14
    bnjwphm
    bnjwpsm
    bnj545.4
    simp2bi
    3ad2ant2
    @5
    bnjwphm
    wa
    @2
    cA
    cR
    vx
    cv
    c-bnj14
    #
    wceq
    #
    bnjwphn
    bnjwphm
    @5
    @4
    @21
    wceq
    @22
    bnj545.1
    @2
    @4
    @21
    eqtr
    sylan2b
    bnj545.7
    sylibr
    syl2anc
end
