include "w-bnj17.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.23vv.mm"
include "albii.mm"
include "19.23v.mm"
include "bitri.mm"
include "cep.mm"
include "wfr.mm"
include "wral.mm"
include "wfn.mm"
include "bnj1071.mm"
include "bnj769.mm"
include "bnj707.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "bnj1123.mm"
include "bnj1118.mm"
include "bnj1097.mm"
include "bnj1109.mm"
include "bnj1093.mm"
include "bnj1090.mm"
include "vex.mm"
include "bnj110.mm"
include "syl2anc.mm"
include "bnj1121.mm"
include "gen2.mm"
include "mpgbi.mm"
include "bnj1034.mm"

theorem bnj1030
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let cX: class X
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwthm: wff th'
  let bnjwtam: wff ta'
  let bnjwetm: wff et'
  let bnjwzem: wff ze'
  let bnjwph0: wff ph0
  assume bnj1030.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1030.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1030.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1030.4: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1030.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1030.6: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1030.7: |- D = ( _om \ { (/) } )
  assume bnj1030.8: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1030.9: |- ( et <-> ( ( f e. K /\ i e. dom f ) -> ( f ` i ) C_ B ) )
  assume bnj1030.10: |- ( rh <-> A. j e. n ( j _E i -> [. j / i ]. et ) )
  assume bnj1030.11: |- ( ph' <-> [. j / i ]. ph )
  assume bnj1030.12: |- ( ps' <-> [. j / i ]. ps )
  assume bnj1030.13: |- ( ch' <-> [. j / i ]. ch )
  assume bnj1030.14: |- ( th' <-> [. j / i ]. th )
  assume bnj1030.15: |- ( ta' <-> [. j / i ]. ta )
  assume bnj1030.16: |- ( ze' <-> [. j / i ]. ze )
  assume bnj1030.17: |- ( et' <-> [. j / i ]. et )
  assume bnj1030.18: |- ( si <-> ( ( j e. n /\ j _E i ) -> et' ) )
  assume bnj1030.19: |- ( ph0 <-> ( i e. n /\ si /\ f e. K /\ i e. dom f ) )

  disjoint A f
  disjoint A i
  disjoint A j
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f j
  disjoint f n
  disjoint f y
  disjoint i j
  disjoint i n
  disjoint i y
  disjoint j n
  disjoint j y
  disjoint n y
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint n z
  disjoint B f
  disjoint B i
  disjoint B n
  disjoint B y
  disjoint B z
  disjoint D i
  disjoint D j
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint R y
  disjoint R z
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint ch j
  disjoint et j
  disjoint f ta
  disjoint i ta
  disjoint j ta
  disjoint n ta
  disjoint f th
  disjoint i th
  disjoint j th
  disjoint n th
  disjoint i ph
  disjoint ta z
  disjoint th z
  assert |- ( ( th /\ ta ) -> _trCl ( X , A , R ) C_ B )

  proof
    wph
    wps
    wch
    wth
    wta
    wze
    vy
    vz
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cK
    cX
    bnj1030.1
    bnj1030.2
    bnj1030.3
    bnj1030.4
    bnj1030.5
    bnj1030.6
    bnj1030.7
    bnj1030.8
    wth
    wta
    wch
    wze
    w-bnj17
    #
    vz
    cv
    cB
    wcel
    #
    wi
    #
    vi
    wal
    vn
    wal
    #
    @0
    vi
    wex
    vn
    wex
    #
    vf
    wex
    @1
    wi
    #
    vf
    @3
    vf
    wal
    @4
    @1
    wi
    #
    vf
    wal
    @5
    @3
    @6
    vf
    @0
    @1
    vn
    vi
    19.23vv
    albii
    @4
    @1
    vf
    19.23v
    bitri
    @2
    vn
    vi
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    vz
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cK
    cX
    bnj1030.4
    bnj1030.5
    bnj1030.3
    bnj1030.6
    bnj1030.9
    @0
    vn
    cv
    #
    cep
    wfr
    #
    wrh
    wet
    wi
    vi
    @7
    wral
    wet
    vi
    @7
    wral
    wth
    wta
    wch
    wze
    @8
    @7
    cD
    wcel
    vf
    cv
    #
    @7
    wfn
    wph
    wps
    @8
    wch
    bnj1030.3
    cD
    vn
    bnj1030.7
    bnj1071
    bnj769
    bnj707
    wch
    wth
    wta
    wet
    wze
    wsi
    wrh
    cB
    vf
    vi
    vj
    vn
    cK
    bnjwetm
    bnjwph0
    bnj1030.9
    bnj1030.10
    bnj1030.17
    bnj1030.18
    bnj1030.19
    wph
    wps
    wch
    wth
    wta
    wze
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vj
    vn
    bnjwph0
    wth
    wta
    wch
    w3a
    bnjwph0
    wa
    vi
    cv
    #
    @9
    cfv
    cB
    wss
    vj
    @10
    c0
    wph
    wps
    wch
    wth
    wta
    wsi
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vj
    vn
    cK
    cX
    bnjwetm
    bnjwph0
    bnj1030.2
    bnj1030.3
    bnj1030.5
    bnj1030.7
    bnj1030.18
    bnj1030.19
    wph
    wps
    wet
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vj
    vn
    cK
    bnjwetm
    bnj1030.2
    bnj1030.8
    bnj1030.9
    bnj1030.17
    bnj1123
    bnj1118
    wph
    wps
    wch
    wth
    wta
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnjwph0
    bnj1030.1
    bnj1030.3
    bnj1030.5
    bnj1097
    bnj1109
    bnj1030.2
    bnj1030.3
    bnj1093
    bnj1090
    wet
    wrh
    vi
    vj
    @7
    cep
    vn
    vex
    bnj1030.10
    bnj110
    syl2anc
    bnj1030.8
    bnj1121
    gen2
    mpgbi
    bnj1034
end
