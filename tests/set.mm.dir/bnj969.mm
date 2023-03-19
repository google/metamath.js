include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "w-bnj17.mm"
include "cvv.mm"
include "simpl.mm"
include "wfn.mm"
include "bnj667.mm"
include "3imtr4i.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "bnj1232.mm"
include "vex.mm"
include "bnj216.mm"
include "id.mm"
include "3anim123i.mm"
include "3ancomb.mm"
include "bitri.mm"
include "sylibr.mm"
include "jca32.mm"
include "bnj256.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "bnj938.mm"
include "syl5eqel.mm"
include "syl.mm"

theorem bnj969
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let wsi: wff si
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cX: class X
  let vp: setvar p
  assume bnj969.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj969.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj969.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj969.10: |- D = ( _om \ { (/) } )
  assume bnj969.12: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj969.14: |- ( ta <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj969.15: |- ( si <-> ( n e. D /\ p = suc n /\ m e. n ) )

  disjoint A i
  disjoint A m
  disjoint A y
  disjoint i m
  disjoint i y
  disjoint m y
  disjoint R i
  disjoint R m
  disjoint R y
  disjoint f i
  disjoint f m
  disjoint f y
  disjoint i n
  disjoint m n
  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> C e. _V )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    wch
    vn
    cv
    #
    vm
    cv
    #
    csuc
    wceq
    #
    vp
    cv
    @3
    csuc
    wceq
    #
    w3a
    #
    wa
    #
    @0
    @1
    wta
    wsi
    w-bnj17
    #
    cC
    cvv
    wcel
    @8
    @2
    wta
    wsi
    wa
    wa
    @9
    @8
    @2
    wta
    wsi
    @2
    @7
    simpl
    @7
    wta
    @2
    wch
    @5
    wta
    @6
    @3
    cD
    wcel
    #
    vf
    cv
    #
    @3
    wfn
    #
    wph
    wps
    w-bnj17
    @12
    wph
    wps
    w3a
    wch
    wta
    @10
    @12
    wph
    wps
    bnj667
    bnj969.3
    bnj969.14
    3imtr4i
    3ad2ant1
    adantl
    @7
    wsi
    @2
    @7
    @10
    @4
    @3
    wcel
    #
    @6
    w3a
    #
    wsi
    wch
    @10
    @5
    @13
    @6
    @6
    wch
    @10
    @12
    wph
    wps
    bnj969.3
    bnj1232
    @3
    @4
    vm
    vex
    bnj216
    @6
    id
    3anim123i
    wsi
    @10
    @6
    @13
    w3a
    @14
    bnj969.15
    @10
    @6
    @13
    3ancomb
    bitri
    sylibr
    adantl
    jca32
    @0
    @1
    wta
    wsi
    bnj256
    sylibr
    @9
    cC
    vy
    @4
    @11
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    cvv
    bnj969.12
    wta
    wsi
    vy
    cA
    cD
    cR
    vf
    vi
    vn
    vp
    cX
    vm
    wph
    wps
    bnj969.10
    bnj969.14
    bnj969.15
    bnj969.1
    bnj969.2
    bnj938
    syl5eqel
    syl
end
