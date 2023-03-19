include "wex.mm"
include "w-bnj17.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "cdm.mm"
include "cfv.mm"
include "c-bnj18.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "bnj258.mm"
include "sylbir.mm"
include "ex.mm"
include "eximdv.mm"
include "bnj985.mm"
include "syl6ibr.mm"
include "imp.mm"
include "sylbi.mm"
include "bnj1019.mm"
include "com.mm"
include "simp3d.mm"
include "wfn.mm"
include "wceq.mm"
include "bnj1235.mm"
include "fndm.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "exlimiv.mm"
include "cvv.mm"
include "bnj918.mm"
include "vex.mm"
include "sucex.mm"
include "bnj1015.mm"
include "syl2anc.mm"

theorem bnj1018
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
  assume bnj1018.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1018.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1018.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1018.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj1018.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj1018.7: |- ( ph' <-> [. p / n ]. ph )
  assume bnj1018.8: |- ( ps' <-> [. p / n ]. ps )
  assume bnj1018.9: |- ( ch' <-> [. p / n ]. ch )
  assume bnj1018.10: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj1018.11: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj1018.12: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj1018.13: |- D = ( _om \ { (/) } )
  assume bnj1018.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1018.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj1018.16: |- G = ( f u. { <. n , C >. } )
  assume bnj1018.26: |- ( ch" <-> ( p e. D /\ G Fn p /\ ph" /\ ps" ) )
  assume bnj1018.29: |- ( ( th /\ ch /\ ta /\ et ) -> ch" )
  assume bnj1018.30: |- ( ( th /\ ch /\ ta /\ et ) -> ( ch" /\ i e. _om /\ suc i e. p ) )

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
  disjoint G p
  disjoint i p
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint ch p
  disjoint et p
  disjoint f p
  disjoint n p
  disjoint i ph
  disjoint p th
  assert |- ( ( th /\ ch /\ et /\ E. p ta ) -> ( G ` suc i ) C_ _trCl ( X , A , R ) )

  proof
    wth
    wch
    wet
    wta
    vp
    wex
    #
    w-bnj17
    #
    cG
    cB
    wcel
    #
    vi
    cv
    #
    csuc
    #
    cG
    cdm
    #
    wcel
    #
    @4
    cG
    cfv
    cA
    cR
    cX
    c-bnj18
    wss
    @1
    wth
    wch
    wet
    w3a
    #
    @0
    wa
    @2
    wth
    wch
    wet
    @0
    df-bnj17
    @7
    @0
    @2
    @7
    @0
    bnjwchn
    vp
    wex
    @2
    @7
    wta
    bnjwchn
    vp
    @7
    wta
    bnjwchn
    @7
    wta
    wa
    wth
    wch
    wta
    wet
    w-bnj17
    #
    bnjwchn
    wth
    wch
    wta
    wet
    bnj258
    bnj1018.29
    sylbir
    ex
    eximdv
    wph
    wps
    wch
    cB
    cC
    cD
    vf
    vn
    cG
    vp
    bnjwchm
    bnjwchn
    bnj1018.3
    bnj1018.9
    bnj1018.12
    bnj1018.14
    bnj1018.16
    bnj985
    syl6ibr
    imp
    sylbi
    @1
    @8
    vp
    wex
    @6
    wch
    wth
    wta
    wet
    vp
    bnj1019
    @8
    @6
    vp
    @8
    @4
    vp
    cv
    #
    @5
    @8
    bnjwchn
    @3
    com
    wcel
    @4
    @9
    wcel
    bnj1018.30
    simp3d
    @8
    bnjwchn
    cG
    @9
    wfn
    #
    @5
    @9
    wceq
    bnj1018.29
    bnjwchn
    @9
    cD
    wcel
    @10
    bnjwphn
    bnjwpsn
    bnj1018.26
    bnj1235
    @9
    cG
    fndm
    3syl
    eleqtrrd
    exlimiv
    sylbir
    wph
    wps
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cG
    @4
    cvv
    cX
    bnj1018.1
    bnj1018.2
    bnj1018.13
    bnj1018.14
    cC
    vf
    vn
    cG
    bnj1018.16
    bnj918
    @3
    vi
    vex
    sucex
    bnj1015
    syl2anc
end
