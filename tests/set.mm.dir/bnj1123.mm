include "cv.mm"
include "wsbc.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "sbcbii.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "nfcv.mm"
include "nfv.mm"
include "csuc.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "com.mm"
include "bnj1095.mm"
include "nf5i.mm"
include "nf3an.mm"
include "nfrex.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "sbciegf.mm"
include "ax-mp.mm"
include "3bitri.mm"

theorem bnj1123
  let wph: wff ph
  let wps: wff ps
  let wet: wff et
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let bnjwetm: wff et'
  assume bnj1123.4: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1123.3: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1123.1: |- ( et <-> ( ( f e. K /\ i e. dom f ) -> ( f ` i ) C_ B ) )
  assume bnj1123.2: |- ( et' <-> [. j / i ]. et )

  disjoint B i
  disjoint D i
  disjoint f i
  disjoint i j
  disjoint i n
  disjoint i ph
  assert |- ( et' <-> ( ( f e. K /\ j e. dom f ) -> ( f ` j ) C_ B ) )

  proof
    bnjwetm
    wet
    vi
    vj
    cv
    #
    wsbc
    vf
    cv
    #
    cK
    wcel
    #
    vi
    cv
    #
    @1
    cdm
    #
    wcel
    #
    wa
    #
    @3
    @1
    cfv
    #
    cB
    wss
    #
    wi
    #
    vi
    @0
    wsbc
    #
    @2
    @0
    @4
    wcel
    #
    wa
    #
    @0
    @1
    cfv
    #
    cB
    wss
    #
    wi
    #
    bnj1123.2
    wet
    @9
    vi
    @0
    bnj1123.1
    sbcbii
    @0
    cvv
    wcel
    @10
    @15
    wb
    vj
    vex
    @9
    @15
    vi
    @0
    cvv
    @12
    @14
    vi
    @2
    @11
    vi
    vi
    vf
    cK
    vi
    cK
    @1
    vn
    cv
    #
    wfn
    #
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    vf
    cab
    bnj1123.3
    @19
    vi
    vf
    @18
    vi
    vn
    cD
    vi
    cD
    nfcv
    @17
    wph
    wps
    vi
    @17
    vi
    nfv
    wph
    vi
    nfv
    wps
    vi
    wps
    @3
    csuc
    #
    @16
    wcel
    @20
    @1
    cfv
    vy
    @7
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    vi
    com
    bnj1123.4
    bnj1095
    nf5i
    nf3an
    nfrex
    nfab
    nfcxfr
    nfcri
    @11
    vi
    nfv
    nfan
    @14
    vi
    nfv
    nfim
    vi
    vj
    weq
    #
    @6
    @12
    @8
    @14
    @21
    @5
    @11
    @2
    @3
    @0
    @4
    eleq1
    anbi2d
    @21
    @7
    @13
    cB
    @3
    @0
    @1
    fveq2
    sseq1d
    imbi12d
    sbciegf
    ax-mp
    3bitri
end
