include "wsbc.mm"
include "cv.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "wal.mm"
include "df-ral.mm"
include "bicomi.mm"
include "sbcbii.mm"
include "cvv.mm"
include "wb.mm"
include "nfv.mm"
include "sbc19.21g.mm"
include "ax-mp.mm"
include "fveq1.mm"
include "bnj1113.mm"
include "eqeq12d.mm"
include "bnj610.mm"
include "imbi2i.mm"
include "bitri.mm"
include "albii.mm"
include "sbcal.mm"
include "3bitr4ri.mm"

theorem bnj611
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let cG: class G
  let cN: class N
  let bnjwpsn: wff ps"
  let ve: setvar e
  assume bnj611.1: |- ( ps <-> A. i e. _om ( suc i e. N -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj611.2: |- ( ps" <-> [. G / f ]. ps )
  assume bnj611.3: |- G e. _V

  disjoint A f
  disjoint G i
  disjoint G y
  disjoint i y
  disjoint N f
  disjoint R f
  disjoint f i
  disjoint f y
  disjoint A e
  disjoint e f
  disjoint G e
  disjoint e i
  disjoint e y
  disjoint R e
  assert |- ( ps" <-> A. i e. _om ( suc i e. N -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) ) )

  proof
    bnjwpsn
    wps
    vf
    cG
    wsbc
    #
    vi
    cv
    #
    csuc
    #
    cN
    wcel
    #
    @2
    cG
    cfv
    #
    vy
    @1
    cG
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    bnj611.2
    @1
    com
    wcel
    #
    @3
    @2
    vf
    cv
    #
    cfv
    #
    vy
    @1
    @12
    cfv
    #
    @6
    ciun
    #
    wceq
    #
    wi
    #
    wi
    #
    vi
    wal
    #
    vf
    cG
    wsbc
    #
    @17
    vi
    com
    wral
    #
    vf
    cG
    wsbc
    @10
    @0
    @19
    @21
    vf
    cG
    @21
    @19
    @17
    vi
    com
    df-ral
    bicomi
    sbcbii
    @18
    vf
    cG
    wsbc
    #
    vi
    wal
    @11
    @9
    wi
    #
    vi
    wal
    @20
    @10
    @22
    @23
    vi
    @22
    @11
    @17
    vf
    cG
    wsbc
    #
    wi
    #
    @23
    cG
    cvv
    wcel
    #
    @22
    @25
    wb
    bnj611.3
    @11
    @17
    vf
    cG
    cvv
    @11
    vf
    nfv
    sbc19.21g
    ax-mp
    @24
    @9
    @11
    @24
    @3
    @16
    vf
    cG
    wsbc
    #
    wi
    #
    @9
    @26
    @24
    @28
    wb
    bnj611.3
    @3
    @16
    vf
    cG
    cvv
    @3
    vf
    nfv
    sbc19.21g
    ax-mp
    @27
    @8
    @3
    @16
    @8
    vf
    ve
    cG
    @2
    ve
    cv
    #
    cfv
    #
    vy
    @1
    @29
    cfv
    #
    @6
    ciun
    #
    wceq
    bnj611.3
    @12
    cG
    wceq
    @13
    @4
    @15
    @7
    @2
    @12
    cG
    fveq1
    vy
    @12
    cG
    @14
    @5
    @6
    @1
    @12
    cG
    fveq1
    bnj1113
    eqeq12d
    @12
    @29
    wceq
    @13
    @30
    @15
    @32
    @2
    @12
    @29
    fveq1
    vy
    @12
    @29
    @14
    @31
    @6
    @1
    @12
    @29
    fveq1
    bnj1113
    eqeq12d
    @29
    cG
    wceq
    @30
    @4
    @32
    @7
    @2
    @29
    cG
    fveq1
    vy
    @29
    cG
    @31
    @5
    @6
    @1
    @29
    cG
    fveq1
    bnj1113
    eqeq12d
    bnj610
    imbi2i
    bitri
    imbi2i
    bitri
    albii
    @18
    vi
    vf
    cG
    sbcal
    @9
    vi
    com
    df-ral
    3bitr4ri
    wps
    @21
    vf
    cG
    bnj611.1
    sbcbii
    3bitr4ri
    bitri
end
