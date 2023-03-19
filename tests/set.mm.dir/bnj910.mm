include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "bnj970.mm"
include "cvv.mm"
include "bnj969.mm"
include "simpr3.mm"
include "bnj1235.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "bnj941.mm"
include "3impib.mm"
include "syl3anc.mm"
include "bnj944.mm"
include "bnj967.mm"
include "bnj966.mm"
include "bnj964.mm"
include "bnj951.mm"
include "vex.mm"
include "bnj919.mm"
include "bnj918.mm"
include "bnj976.mm"
include "sylibr.mm"

theorem bnj910
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let wsi: wff si
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwchn: wff ch"
  assume bnj910.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj910.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj910.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj910.4: |- ( ph' <-> [. p / n ]. ph )
  assume bnj910.5: |- ( ps' <-> [. p / n ]. ps )
  assume bnj910.6: |- ( ch' <-> [. p / n ]. ch )
  assume bnj910.7: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj910.8: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj910.9: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj910.10: |- D = ( _om \ { (/) } )
  assume bnj910.11: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj910.12: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj910.13: |- G = ( f u. { <. n , C >. } )
  assume bnj910.14: |- ( ta <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj910.15: |- ( si <-> ( n e. D /\ p = suc n /\ m e. n ) )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f y
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint m n
  disjoint m y
  disjoint n y
  disjoint D f
  disjoint D i
  disjoint D n
  disjoint G i
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint f p
  disjoint i p
  disjoint n p
  disjoint i ph
  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> ch" )

  proof
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    wa
    #
    wch
    vn
    cv
    #
    vm
    cv
    csuc
    wceq
    #
    vp
    cv
    #
    @1
    csuc
    wceq
    #
    w3a
    #
    wa
    #
    @3
    cD
    wcel
    #
    cG
    @3
    wfn
    #
    bnjwphn
    bnjwpsn
    w-bnj17
    bnjwchn
    @7
    @8
    bnjwphn
    bnjwpsn
    @6
    wph
    wps
    wch
    cA
    cD
    cR
    vf
    vm
    vn
    cX
    vp
    bnj910.3
    bnj910.10
    bnj970
    @6
    cC
    cvv
    wcel
    #
    @4
    vf
    cv
    #
    @1
    wfn
    #
    @8
    wph
    wps
    wch
    wta
    wsi
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cX
    vp
    bnj910.1
    bnj910.2
    bnj910.3
    bnj910.10
    bnj910.12
    bnj910.14
    bnj910.15
    bnj969
    #
    @0
    wch
    @2
    @4
    simpr3
    @5
    @11
    @0
    wch
    @2
    @11
    @4
    wch
    @1
    cD
    wcel
    @11
    wph
    wps
    bnj910.3
    bnj1235
    3ad2ant1
    adantl
    @9
    @4
    @11
    @8
    cC
    vf
    vn
    cG
    vp
    bnj910.13
    bnj941
    3impib
    syl3anc
    #
    wph
    wps
    wch
    wta
    wsi
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cX
    vp
    bnjwphm
    bnjwphn
    bnj910.1
    bnj910.2
    bnj910.3
    bnj910.4
    bnj910.7
    bnj910.10
    bnj910.12
    bnj910.13
    bnj910.14
    bnj910.15
    bnj944
    wph
    wps
    wch
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cX
    vp
    bnjwpsm
    bnjwpsn
    bnj910.2
    bnj910.3
    bnj910.5
    bnj910.8
    bnj910.12
    bnj910.13
    wph
    wps
    wch
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cX
    vp
    bnj910.2
    bnj910.3
    bnj910.10
    bnj910.12
    bnj910.13
    @12
    bnj967
    wph
    wps
    wch
    vy
    cA
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cX
    vp
    bnj910.3
    bnj910.10
    bnj910.12
    bnj910.13
    @12
    @13
    bnj966
    bnj964
    bnj951
    bnjwphm
    bnjwpsm
    bnjwchm
    cD
    vf
    cG
    @3
    bnjwphn
    bnjwpsn
    bnjwchn
    wph
    wps
    wch
    cD
    @3
    vn
    @10
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj910.3
    bnj910.4
    bnj910.5
    bnj910.6
    vp
    vex
    bnj919
    bnj910.7
    bnj910.8
    bnj910.9
    cC
    vf
    vn
    cG
    bnj910.13
    bnj918
    bnj976
    sylibr
end
