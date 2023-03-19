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
include "ax-5.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfcxfr.mm"
include "nfop.mm"
include "nfsn.mm"
include "nfun.mm"
include "nffv.mm"
include "nfcrii.mm"
include "bnj1316.mm"
include "syl.mm"
include "eqeq12d.mm"
include "bnj956.mm"
include "bnj610.mm"
include "imbi2i.mm"
include "bitri.mm"
include "albii.mm"
include "sbcal.mm"
include "3bitr4ri.mm"

theorem bnj1000
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cN: class N
  let bnjwpsn: wff ps"
  let ve: setvar e
  let vw: setvar w
  assume bnj1000.1: |- ( ps <-> A. i e. _om ( suc i e. N -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1000.2: |- ( ps" <-> [. G / f ]. ps )
  assume bnj1000.3: |- G e. _V
  assume bnj1000.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj1000.16: |- G = ( f u. { <. n , C >. } )

  disjoint A f
  disjoint G i
  disjoint N f
  disjoint R f
  disjoint f i
  disjoint f y
  disjoint i y
  disjoint n y
  disjoint A e
  disjoint e f
  disjoint C w
  disjoint G e
  disjoint G w
  disjoint e i
  disjoint e w
  disjoint i w
  disjoint R e
  disjoint e y
  disjoint f w
  disjoint w y
  disjoint n w
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
    bnj1000.2
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
    bnj1000.3
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
    bnj1000.3
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
    bnj1000.3
    @12
    cG
    wceq
    #
    @13
    @4
    @15
    @7
    @2
    @12
    cG
    fveq1
    @33
    @14
    @5
    wceq
    @15
    @7
    wceq
    @1
    @12
    cG
    fveq1
    vy
    vw
    @14
    @5
    @6
    vw
    cv
    #
    @14
    wcel
    vy
    ax-5
    vy
    vw
    @5
    vy
    @1
    cG
    vy
    cG
    @12
    vn
    cv
    #
    cC
    cop
    #
    csn
    #
    cun
    bnj1000.16
    vy
    @12
    @37
    vy
    @12
    nfcv
    vy
    @36
    vy
    @35
    cC
    vy
    @35
    nfcv
    vy
    cC
    vy
    vm
    cv
    @12
    cfv
    #
    @6
    ciun
    bnj1000.15
    vy
    @38
    @6
    nfiu1
    nfcxfr
    nfop
    nfsn
    nfun
    nfcxfr
    vy
    @1
    nfcv
    nffv
    nfcrii
    #
    bnj1316
    syl
    eqeq12d
    @12
    @29
    wceq
    #
    @13
    @30
    @15
    @32
    @2
    @12
    @29
    fveq1
    @40
    @14
    @31
    wceq
    #
    @15
    @32
    wceq
    @1
    @12
    @29
    fveq1
    vy
    @14
    @31
    @6
    @41
    vy
    ax-5
    bnj956
    syl
    eqeq12d
    @29
    cG
    wceq
    #
    @30
    @4
    @32
    @7
    @2
    @29
    cG
    fveq1
    @42
    @31
    @5
    wceq
    @32
    @7
    wceq
    @1
    @29
    cG
    fveq1
    vy
    vw
    @31
    @5
    @6
    @34
    @31
    wcel
    vy
    ax-5
    @39
    bnj1316
    syl
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
    bnj1000.1
    sbcbii
    3bitr4ri
    bitri
end
