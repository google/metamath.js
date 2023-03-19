include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bnj865.mm"
include "wss.mm"
include "wfn.mm"
include "w3a.mm"
include "cab.mm"
include "bnj873.mm"
include "wel.mm"
include "df-rex.mm"
include "19.29.mm"
include "an12.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "id.mm"
include "wsbc.mm"
include "bnj581.mm"
include "bitr3i.mm"
include "weu.mm"
include "bnj864.mm"
include "exancom.mm"
include "sylbb.mm"
include "nfeu1.mm"
include "nfe1.mm"
include "nfan.mm"
include "nfsbc1v.mm"
include "nfv.mm"
include "nfim.mm"
include "weq.mm"
include "sbceq1a.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "eupick.mm"
include "chvar.mm"
include "syl2an.mm"
include "syl5bir.mm"
include "ex.mm"
include "embantd.mm"
include "impd.mm"
include "sylbir.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "syl5.mm"
include "expdimp.mm"
include "abssdv.mm"
include "syl5eqss.mm"
include "vex.mm"
include "ssex.mm"
include "syl.mm"
include "mpi.mm"

theorem bnj849
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwthm: wff th'
  let vw: setvar w
  assume bnj849.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj849.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj849.3: |- D = ( _om \ { (/) } )
  assume bnj849.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj849.5: |- ( ch <-> ( R _FrSe A /\ X e. A /\ n e. D ) )
  assume bnj849.6: |- ( th <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj849.7: |- ( ph' <-> [. g / f ]. ph )
  assume bnj849.8: |- ( ps' <-> [. g / f ]. ps )
  assume bnj849.9: |- ( th' <-> [. g / f ]. th )
  assume bnj849.10: |- ( ta <-> ( R _FrSe A /\ X e. A ) )

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint B g
  disjoint D f
  disjoint D g
  disjoint D n
  disjoint f g
  disjoint g n
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X n
  disjoint ch f
  disjoint ch g
  disjoint g ph
  disjoint g ps
  disjoint g ta
  disjoint n ta
  disjoint g th
  disjoint A w
  disjoint f w
  disjoint n w
  disjoint B w
  disjoint g w
  disjoint D w
  disjoint R w
  disjoint X w
  disjoint ph w
  disjoint ps w
  disjoint ta w
  assert |- ( ( R _FrSe A /\ X e. A ) -> B e. _V )

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
    wta
    cB
    cvv
    wcel
    #
    bnj849.10
    wta
    wch
    wth
    vf
    vw
    cv
    #
    wrex
    #
    wi
    #
    vn
    wal
    #
    vw
    wex
    @3
    wph
    wps
    wch
    wth
    vy
    vw
    cA
    cD
    cR
    vf
    vi
    vn
    cX
    bnj849.1
    bnj849.2
    bnj849.3
    bnj849.5
    bnj849.6
    bnj865
    wta
    @7
    @3
    vw
    wta
    @7
    @3
    wta
    @7
    wa
    #
    cB
    @4
    wss
    @3
    @8
    cB
    vg
    cv
    #
    vn
    cv
    #
    wfn
    bnjwphm
    bnjwpsm
    w3a
    #
    vn
    cD
    wrex
    #
    vg
    cab
    @4
    wph
    wps
    cB
    cD
    vf
    vg
    vn
    bnjwphm
    bnjwpsm
    bnj849.4
    bnj849.7
    bnj849.8
    bnj873
    @8
    @12
    vg
    @4
    @12
    @10
    cD
    wcel
    #
    @11
    wa
    #
    vn
    wex
    #
    @8
    vg
    vw
    wel
    #
    @11
    vn
    cD
    df-rex
    wta
    @7
    @15
    @16
    @7
    @15
    wa
    @6
    @14
    wa
    #
    vn
    wex
    wta
    @16
    @6
    @14
    vn
    19.29
    wta
    @17
    @16
    vn
    @17
    @13
    @6
    @11
    wa
    #
    wa
    wta
    @16
    @6
    @13
    @11
    an12
    wta
    @13
    @18
    @16
    wta
    @13
    wa
    #
    wch
    @18
    @16
    wi
    @0
    @1
    @13
    w3a
    @2
    @13
    wa
    wch
    @19
    @0
    @1
    @13
    df-3an
    bnj849.5
    wta
    @2
    @13
    bnj849.10
    anbi1i
    3bitr4i
    wch
    @6
    @11
    @16
    wch
    wch
    @5
    @11
    @16
    wi
    #
    wch
    id
    wch
    @5
    @20
    @11
    wth
    vf
    @9
    wsbc
    #
    wch
    @5
    wa
    @16
    @21
    bnjwthm
    @11
    bnj849.9
    wph
    wps
    wth
    vf
    vg
    vn
    bnjwphm
    bnjwpsm
    bnjwthm
    bnj849.6
    bnj849.7
    bnj849.8
    bnj849.9
    bnj581
    bitr3i
    wch
    wth
    vf
    weu
    #
    wth
    vf
    vw
    wel
    #
    wa
    #
    vf
    wex
    #
    @21
    @16
    wi
    #
    @5
    wph
    wps
    wch
    wth
    vy
    cA
    cD
    cR
    vf
    vi
    vn
    cX
    bnj849.1
    bnj849.2
    bnj849.3
    bnj849.5
    bnj849.6
    bnj864
    @5
    @23
    wth
    wa
    vf
    wex
    @25
    wth
    vf
    @4
    df-rex
    @23
    wth
    vf
    exancom
    sylbb
    @22
    @25
    wa
    #
    wth
    @23
    wi
    #
    wi
    @27
    @26
    wi
    vf
    vg
    @27
    @26
    vf
    @22
    @25
    vf
    wth
    vf
    nfeu1
    @24
    vf
    nfe1
    nfan
    @21
    @16
    vf
    wth
    vf
    @9
    nfsbc1v
    @16
    vf
    nfv
    nfim
    nfim
    vf
    vg
    weq
    #
    @28
    @26
    @27
    @29
    wth
    @21
    @23
    @16
    wth
    vf
    @9
    sbceq1a
    vf
    vg
    vw
    elequ1
    imbi12d
    imbi2d
    wth
    @23
    vf
    eupick
    chvar
    syl2an
    syl5bir
    ex
    embantd
    impd
    sylbir
    expimpd
    syl5bi
    exlimdv
    syl5
    expdimp
    syl5bi
    abssdv
    syl5eqss
    cB
    @4
    vw
    vex
    ssex
    syl
    ex
    exlimdv
    mpi
    sylbir
end
