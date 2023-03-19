include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wfn.mm"
include "w3a.mm"
include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "weu.mm"
include "bnj852.mm"
include "com.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "omex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "zfrep6.mm"
include "vtocl.mm"
include "syl.mm"
include "19.37v.mm"
include "mpbir.mm"
include "df-ral.mm"
include "imbi2i.mm"
include "19.21v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "impexp.mm"
include "df-3an.mm"
include "bicomi.mm"
include "imbi1i.mm"
include "bitr3i.mm"
include "albii.mm"
include "bitri.mm"
include "mpbi.mm"
include "rexbii.mm"

theorem bnj865
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let vz: setvar z
  assume bnj865.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj865.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj865.3: |- D = ( _om \ { (/) } )
  assume bnj865.5: |- ( ch <-> ( R _FrSe A /\ X e. A /\ n e. D ) )
  assume bnj865.6: |- ( th <-> ( f Fn n /\ ph /\ ps ) )

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
  disjoint A w
  disjoint f w
  disjoint n w
  disjoint D f
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint R w
  disjoint X f
  disjoint X n
  disjoint X w
  disjoint ph w
  disjoint ps w
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint n z
  disjoint y z
  disjoint D z
  disjoint R z
  disjoint X z
  disjoint w z
  disjoint ph z
  disjoint ps z
  assert |- E. w A. n ( ch -> E. f e. w th )

  proof
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
    wch
    vf
    cv
    vn
    cv
    #
    wfn
    wph
    wps
    w3a
    #
    vf
    @0
    wrex
    #
    wi
    #
    vn
    wal
    #
    vw
    wex
    #
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    @4
    cD
    wcel
    #
    w3a
    #
    @6
    wi
    #
    vn
    wal
    #
    vw
    wex
    #
    @9
    @10
    @11
    wa
    #
    @6
    vn
    cD
    wral
    #
    wi
    #
    vw
    wex
    #
    @16
    @20
    @17
    @18
    vw
    wex
    #
    wi
    @17
    @5
    vf
    weu
    #
    vn
    cD
    wral
    #
    @21
    wph
    wps
    vy
    cA
    cD
    cR
    vf
    vi
    vn
    cX
    bnj865.1
    bnj865.2
    bnj865.3
    bnj852
    @22
    vn
    vz
    cv
    #
    wral
    #
    @6
    vn
    @24
    wral
    #
    vw
    wex
    #
    wi
    @23
    @21
    wi
    vz
    cD
    cD
    com
    c0
    csn
    #
    cdif
    #
    cvv
    bnj865.3
    com
    cvv
    wcel
    @29
    cvv
    wcel
    omex
    com
    @28
    cvv
    difexg
    ax-mp
    eqeltri
    @24
    cD
    wceq
    #
    @25
    @23
    @27
    @21
    @22
    vn
    @24
    cD
    raleq
    @30
    @26
    @18
    vw
    @6
    vn
    @24
    cD
    raleq
    exbidv
    imbi12d
    @5
    vn
    vf
    vz
    vw
    zfrep6
    vtocl
    syl
    @17
    @18
    vw
    19.37v
    mpbir
    @20
    @17
    @12
    @6
    wi
    #
    wi
    #
    vn
    wal
    #
    vw
    wex
    @16
    @19
    @33
    vw
    @19
    @17
    @31
    vn
    wal
    #
    wi
    @33
    @18
    @34
    @17
    @6
    vn
    cD
    df-ral
    imbi2i
    @17
    @31
    vn
    19.21v
    bitr4i
    exbii
    @33
    @15
    vw
    @32
    @14
    vn
    @32
    @17
    @12
    wa
    #
    @6
    wi
    @14
    @17
    @12
    @6
    impexp
    @35
    @13
    @6
    @13
    @35
    @10
    @11
    @12
    df-3an
    bicomi
    imbi1i
    bitr3i
    albii
    exbii
    bitri
    mpbi
    @15
    @8
    vw
    @14
    @7
    vn
    @13
    wch
    @6
    wch
    @13
    bnj865.5
    bicomi
    imbi1i
    albii
    exbii
    mpbi
    @3
    @8
    vw
    @2
    @7
    vn
    @1
    @6
    wch
    wth
    @5
    vf
    @0
    bnj865.6
    rexbii
    imbi2i
    albii
    exbii
    mpbir
end
