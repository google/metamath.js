include "w-bnj17.mm"
include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "c-bnj18.mm"
include "c-bnj14.mm"
include "bnj253.mm"
include "simp1bi.mm"
include "sylbi.mm"
include "bnj705.mm"
include "bnj643.mm"
include "com.mm"
include "3simpc.mm"
include "bnj707.mm"
include "bnj255.mm"
include "syl3anbrc.mm"
include "bnj252.mm"
include "sylib.mm"
include "wfn.mm"
include "biid.mm"
include "bnj910.mm"
include "syl.mm"

theorem bnj998
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vy: setvar y
  let vz: setvar z
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
  assume bnj998.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj998.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj998.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj998.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj998.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj998.7: |- ( ph' <-> [. p / n ]. ph )
  assume bnj998.8: |- ( ps' <-> [. p / n ]. ps )
  assume bnj998.9: |- ( ch' <-> [. p / n ]. ch )
  assume bnj998.10: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj998.11: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj998.12: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj998.13: |- D = ( _om \ { (/) } )
  assume bnj998.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj998.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj998.16: |- G = ( f u. { <. n , C >. } )

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
  assert |- ( ( th /\ ch /\ ta /\ et ) -> ch" )

  proof
    wth
    wch
    wta
    wet
    w-bnj17
    #
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
    @4
    csuc
    wceq
    #
    w3a
    wa
    #
    bnjwchn
    @0
    @3
    wch
    @6
    @7
    w-bnj17
    #
    @8
    @0
    @3
    wch
    @6
    @7
    wa
    #
    @9
    wth
    wch
    wta
    wet
    @3
    wth
    @1
    @2
    vy
    cv
    #
    cA
    cR
    cX
    c-bnj18
    wcel
    #
    vz
    cv
    cA
    cR
    @11
    c-bnj14
    wcel
    #
    w-bnj17
    #
    @3
    bnj998.4
    @14
    @3
    @12
    @13
    @1
    @2
    @12
    @13
    bnj253
    simp1bi
    sylbi
    bnj705
    wth
    wch
    wta
    wet
    bnj643
    wth
    wch
    wta
    wet
    @10
    wta
    @5
    com
    wcel
    #
    @6
    @7
    w3a
    @10
    bnj998.5
    @15
    @6
    @7
    3simpc
    sylbi
    bnj707
    @3
    wch
    @6
    @7
    bnj255
    syl3anbrc
    @3
    wch
    @6
    @7
    bnj252
    sylib
    wph
    wps
    wch
    vf
    cv
    @4
    wfn
    wph
    wps
    w3a
    #
    @4
    cD
    wcel
    @7
    @5
    @4
    wcel
    w3a
    #
    vy
    cA
    cB
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
    bnjwpsm
    bnjwchm
    bnjwphn
    bnjwpsn
    bnjwchn
    bnj998.1
    bnj998.2
    bnj998.3
    bnj998.7
    bnj998.8
    bnj998.9
    bnj998.10
    bnj998.11
    bnj998.12
    bnj998.13
    bnj998.14
    bnj998.15
    bnj998.16
    @16
    biid
    @17
    biid
    bnj910
    syl
end
