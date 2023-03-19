include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "w-bnj17.mm"
include "c-bnj14.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "wfn.mm"
include "vex.mm"
include "bnj919.mm"
include "bnj918.mm"
include "bnj976.mm"
include "bnj1254.mm"
include "anim1i.mm"
include "bnj252.mm"
include "3imtr4i.mm"
include "ciun.mm"
include "ssiun2.mm"
include "bnj708.mm"
include "wceq.mm"
include "3simpa.mm"
include "ancomd.mm"
include "simp3.mm"
include "wi.mm"
include "bnj539.mm"
include "bnj965.mm"
include "bnj228.mm"
include "sylc.mm"
include "bnj721.mm"
include "sseqtr4d.mm"
include "syl.mm"

theorem bnj999
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vy: setvar y
  let cA: class A
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
  assume bnj999.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj999.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj999.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj999.7: |- ( ph' <-> [. p / n ]. ph )
  assume bnj999.8: |- ( ps' <-> [. p / n ]. ps )
  assume bnj999.9: |- ( ch' <-> [. p / n ]. ch )
  assume bnj999.10: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj999.11: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj999.12: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj999.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj999.16: |- G = ( f u. { <. n , C >. } )

  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint A f
  disjoint A n
  disjoint D f
  disjoint D n
  disjoint G i
  disjoint R f
  disjoint R n
  disjoint X f
  disjoint X n
  disjoint f p
  disjoint i p
  disjoint n p
  assert |- ( ( ch" /\ i e. _om /\ suc i e. p /\ y e. ( G ` i ) ) -> _pred ( y , A , R ) C_ ( G ` suc i ) )

  proof
    bnjwchn
    vi
    cv
    #
    com
    wcel
    #
    @0
    csuc
    #
    vp
    cv
    #
    wcel
    #
    vy
    cv
    #
    @0
    cG
    cfv
    #
    wcel
    #
    w-bnj17
    #
    bnjwpsn
    @1
    @4
    @7
    w-bnj17
    #
    cA
    cR
    @5
    c-bnj14
    #
    @2
    cG
    cfv
    #
    wss
    bnjwchn
    @1
    @4
    @7
    w3a
    #
    wa
    bnjwpsn
    @12
    wa
    @8
    @9
    bnjwchn
    bnjwpsn
    @12
    bnjwchn
    @3
    cD
    wcel
    cG
    @3
    wfn
    bnjwphn
    bnjwpsn
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
    vf
    cv
    #
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj999.3
    bnj999.7
    bnj999.8
    bnj999.9
    vp
    vex
    #
    bnj919
    bnj999.10
    bnj999.11
    bnj999.12
    cC
    vf
    vn
    cG
    bnj999.16
    bnj918
    bnj976
    bnj1254
    anim1i
    bnjwchn
    @1
    @4
    @7
    bnj252
    bnjwpsn
    @1
    @4
    @7
    bnj252
    3imtr4i
    @9
    @10
    vy
    @6
    @10
    ciun
    #
    @11
    bnjwpsn
    @1
    @4
    @7
    @10
    @15
    wss
    vy
    @6
    @10
    ssiun2
    bnj708
    bnjwpsn
    @1
    @4
    @7
    @11
    @15
    wceq
    #
    bnjwpsn
    @1
    @4
    w3a
    #
    @1
    bnjwpsn
    wa
    @4
    @16
    @17
    bnjwpsn
    @1
    bnjwpsn
    @1
    @4
    3simpa
    ancomd
    bnjwpsn
    @1
    @4
    simp3
    bnjwpsn
    @4
    @16
    wi
    vi
    com
    bnjwpsm
    vy
    cA
    cC
    cR
    vf
    vi
    vm
    vn
    cG
    @3
    bnjwpsn
    wps
    vy
    cA
    cR
    vi
    vn
    @13
    @3
    bnjwpsm
    bnj999.2
    bnj999.8
    @14
    bnj539
    bnj999.11
    bnj999.15
    bnj999.16
    bnj965
    bnj228
    sylc
    bnj721
    sseqtr4d
    syl
end
