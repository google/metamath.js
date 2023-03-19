include "w-bnj15.mm"
include "w3a.mm"
include "cv.mm"
include "com.mm"
include "wcel.mm"
include "w-bnj17.mm"
include "csuc.mm"
include "wceq.mm"
include "wfn.mm"
include "wa.mm"
include "bnj257.mm"
include "bnj268.mm"
include "bitri.mm"
include "bnj253.mm"
include "bnj256.mm"
include "3bitr3i.mm"
include "3anbi1i.mm"
include "bnj170.mm"
include "3anan32.mm"
include "anbi12i.mm"
include "3bitr4ri.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bnj252.mm"
include "3bitr4i.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "eqeq2i.mm"
include "3anbi2i.mm"
include "biid.mm"
include "bnj535.mm"
include "sylbi.mm"

theorem bnj543
  let wta: wff ta
  let wsi: wff si
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj543.1: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj543.2: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj543.3: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj543.4: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj543.5: |- ( si <-> ( m e. _om /\ n = suc m /\ p e. m ) )

  disjoint A i
  disjoint A p
  disjoint A y
  disjoint i p
  disjoint i y
  disjoint p y
  disjoint R i
  disjoint R p
  disjoint R y
  disjoint f i
  disjoint f p
  disjoint f y
  disjoint i m
  disjoint m p
  disjoint p ph'
  assert |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wsi
    w3a
    #
    @0
    bnjwphm
    bnjwpsm
    vm
    cv
    #
    com
    wcel
    #
    vp
    cv
    @2
    wcel
    #
    w-bnj17
    #
    vn
    cv
    #
    @2
    csuc
    #
    wceq
    #
    vf
    cv
    @2
    wfn
    #
    w-bnj17
    #
    cG
    @6
    wfn
    #
    @0
    wta
    wsi
    wa
    #
    wa
    @0
    @5
    @8
    @9
    w3a
    #
    wa
    #
    @1
    @10
    @12
    @13
    @0
    bnjwphm
    bnjwpsm
    wa
    #
    @3
    @4
    wa
    #
    wa
    #
    @8
    @9
    w3a
    #
    @15
    @9
    wa
    #
    @16
    @8
    wa
    #
    wa
    #
    @13
    @12
    @15
    @16
    @8
    @9
    w-bnj17
    #
    @15
    @9
    @16
    @8
    w-bnj17
    #
    @18
    @21
    @22
    @15
    @16
    @9
    @8
    w-bnj17
    @23
    @15
    @16
    @8
    @9
    bnj257
    @15
    @16
    @9
    @8
    bnj268
    bitri
    @15
    @16
    @8
    @9
    bnj253
    @15
    @9
    @16
    @8
    bnj256
    3bitr3i
    @5
    @17
    @8
    @9
    bnjwphm
    bnjwpsm
    @3
    @4
    bnj256
    3anbi1i
    wta
    @19
    wsi
    @20
    wta
    @9
    bnjwphm
    bnjwpsm
    w3a
    @19
    bnj543.4
    @9
    bnjwphm
    bnjwpsm
    bnj170
    bitri
    wsi
    @3
    @8
    @4
    w3a
    @20
    bnj543.5
    @3
    @8
    @4
    3anan32
    bitri
    anbi12i
    3bitr4ri
    anbi2i
    @0
    wta
    wsi
    3anass
    @0
    @5
    @8
    @9
    bnj252
    #
    3bitr4i
    @10
    @0
    @5
    @6
    @2
    @2
    csn
    cun
    #
    wceq
    #
    @9
    w-bnj17
    #
    @11
    @14
    @0
    @5
    @26
    @9
    w3a
    #
    wa
    @10
    @27
    @13
    @28
    @0
    @8
    @26
    @5
    @9
    @7
    @25
    @6
    @2
    df-suc
    eqeq2i
    3anbi2i
    anbi2i
    @24
    @0
    @5
    @26
    @9
    bnj252
    3bitr4i
    @5
    vx
    vy
    cA
    cR
    vf
    vi
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    bnj543.1
    bnj543.2
    bnj543.3
    @5
    biid
    bnj535
    sylbi
    sylbi
end
