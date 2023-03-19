include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "w3a.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "simp1bi.mm"
include "bnj581.mm"
include "bnj240.mm"
include "cep.mm"
include "wfr.mm"
include "wel.mm"
include "bnj154.mm"
include "vex.mm"
include "bnj540.mm"
include "bnj591.mm"
include "bnj594.mm"
include "ex.mm"
include "rgen.mm"
include "bnj110.mm"
include "mpan2.mm"
include "ralbii.mm"
include "sylib.mm"
include "r19.21be.mm"
include "com.mm"
include "word.mm"
include "bnj923.mm"
include "nnord.mm"
include "ordfr.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "pm4.71ri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "mpbir.mm"
include "r19.21v.mm"
include "mpbi.mm"
include "eqfnfv.mm"
include "biimprd.mm"
include "sylc.mm"
include "3expib.mm"
include "alrimivv.mm"
include "wsb.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "anbi2i.mm"
include "2albii.mm"
include "nfv.mm"
include "mo3.mm"
include "3bitr4i.mm"
include "sylibr.mm"

theorem bnj580
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj580.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj580.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj580.3: |- ( ch <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj580.4: |- ( ph' <-> [. g / f ]. ph )
  assume bnj580.5: |- ( ps' <-> [. g / f ]. ps )
  assume bnj580.6: |- ( ch' <-> [. g / f ]. ch )
  assume bnj580.7: |- D = ( _om \ { (/) } )
  assume bnj580.8: |- ( th <-> ( ( n e. D /\ ch /\ ch' ) -> ( f ` j ) = ( g ` j ) ) )
  assume bnj580.9: |- ( ta <-> A. k e. n ( k _E j -> [. k / j ]. th ) )

  disjoint A f
  disjoint A i
  disjoint A k
  disjoint f i
  disjoint f k
  disjoint i k
  disjoint D f
  disjoint D g
  disjoint D j
  disjoint D k
  disjoint f g
  disjoint f j
  disjoint g j
  disjoint g k
  disjoint j k
  disjoint R f
  disjoint R i
  disjoint R k
  disjoint ch g
  disjoint ch j
  disjoint ch k
  disjoint ch' j
  disjoint ch' k
  disjoint f n
  disjoint g i
  disjoint g n
  disjoint i n
  disjoint k n
  disjoint f x
  disjoint f y
  disjoint g y
  disjoint i y
  disjoint k y
  disjoint j n
  disjoint k th
  assert |- ( n e. D -> E* f ch )

  proof
    vn
    cv
    #
    cD
    wcel
    #
    wch
    bnjwchm
    wa
    #
    vf
    vg
    weq
    #
    wi
    #
    vg
    wal
    vf
    wal
    #
    wch
    vf
    wmo
    #
    @1
    @4
    vf
    vg
    @1
    wch
    bnjwchm
    @3
    @1
    wch
    bnjwchm
    w3a
    #
    vf
    cv
    #
    @0
    wfn
    #
    vg
    cv
    #
    @0
    wfn
    #
    wa
    #
    vj
    cv
    #
    @8
    cfv
    @13
    @10
    cfv
    wceq
    #
    vj
    @0
    wral
    #
    @3
    @1
    wch
    bnjwchm
    @9
    @11
    wch
    @9
    wph
    wps
    bnj580.3
    simp1bi
    bnjwchm
    @11
    bnjwphm
    bnjwpsm
    wph
    wps
    wch
    vf
    vg
    vn
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj580.3
    bnj580.4
    bnj580.5
    bnj580.6
    bnj581
    #
    simp1bi
    bnj240
    @7
    @14
    wi
    #
    vj
    @0
    wral
    #
    @7
    @15
    wi
    @18
    @0
    cep
    wfr
    #
    @17
    wi
    #
    vj
    @0
    wral
    @19
    @17
    vj
    @0
    @19
    wth
    vj
    @0
    wral
    #
    @18
    @19
    wta
    wth
    wi
    #
    vj
    @0
    wral
    @21
    @22
    vj
    @0
    vj
    vn
    wel
    wta
    wth
    wph
    wps
    wch
    wth
    wta
    vx
    vy
    cA
    cD
    cR
    vf
    vg
    vi
    vj
    vk
    vn
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj580.1
    bnj580.2
    bnj580.3
    bnj580.7
    vx
    cA
    cR
    vf
    vg
    wph
    bnjwphm
    bnj580.4
    bnj580.1
    bnj154
    wps
    vy
    cA
    cR
    vf
    vi
    @10
    @0
    bnjwpsm
    bnj580.2
    bnj580.5
    vg
    vex
    bnj540
    @16
    bnj580.8
    wch
    wth
    cD
    vf
    vg
    vj
    vk
    vn
    bnjwchm
    bnj580.8
    bnj591
    bnj580.9
    bnj594
    ex
    rgen
    wth
    wta
    vj
    vk
    @0
    cep
    vn
    vex
    bnj580.9
    bnj110
    mpan2
    wth
    @17
    vj
    @0
    bnj580.8
    ralbii
    sylib
    r19.21be
    @17
    @20
    vj
    @0
    @17
    @19
    @7
    wa
    #
    @14
    wi
    @20
    @7
    @23
    @14
    @7
    @19
    @1
    wch
    @19
    bnjwchm
    @1
    @0
    com
    wcel
    @0
    word
    @19
    cD
    vn
    bnj580.7
    bnj923
    @0
    nnord
    @0
    ordfr
    3syl
    3ad2ant1
    pm4.71ri
    imbi1i
    @19
    @7
    @14
    impexp
    bitri
    ralbii
    mpbir
    @7
    @14
    vj
    @0
    r19.21v
    mpbi
    @12
    @3
    @15
    vj
    @0
    @8
    @10
    eqfnfv
    biimprd
    sylc
    3expib
    alrimivv
    wch
    wch
    vf
    vg
    wsb
    #
    wa
    #
    @3
    wi
    #
    vg
    wal
    vf
    wal
    wch
    wch
    vf
    @10
    wsbc
    #
    wa
    #
    @3
    wi
    #
    vg
    wal
    vf
    wal
    @6
    @5
    @26
    @29
    vf
    vg
    @25
    @28
    @3
    @24
    @27
    wch
    wch
    vf
    vg
    sbsbc
    anbi2i
    imbi1i
    2albii
    wch
    vf
    vg
    wch
    vg
    nfv
    mo3
    @4
    @29
    vf
    vg
    @2
    @28
    @3
    bnjwchm
    @27
    wch
    bnj580.6
    anbi2i
    imbi1i
    2albii
    3bitr4i
    sylibr
end
