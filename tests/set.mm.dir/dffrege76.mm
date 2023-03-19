include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "csn.mm"
include "cv.mm"
include "cun.mm"
include "cima.mm"
include "wss.mm"
include "cab.mm"
include "cint.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wel.mm"
include "wb.mm"
include "brtrclfv2.mm"
include "mp3an.mm"
include "elexi.mm"
include "elintab.mm"
include "wa.mm"
include "imaundi.mm"
include "equncomi.mm"
include "sseq1i.mm"
include "unss.mm"
include "bitr4i.mm"
include "df-he.mm"
include "bicomi.mm"
include "dfss2.mm"
include "cop.mm"
include "vex.mm"
include "elimasn.mm"
include "df-br.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"
include "anbi12i.mm"
include "impexp.mm"
include "3bitrri.mm"

theorem dffrege76
  let cB: class B
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cV: class V
  let cW: class W
  let va: setvar a
  assume frege76.b: |- B e. U
  assume frege76.e: |- E e. V
  assume frege76.r: |- R e. W

  disjoint a f
  disjoint B a
  disjoint B f
  disjoint E f
  disjoint R a
  disjoint R f
  disjoint U f
  disjoint V f
  disjoint W f
  assert |- ( A. f ( R hereditary f -> ( A. a ( B R a -> a e. f ) -> E e. f ) ) <-> B ( t+ ` R ) E )

  proof
    cB
    cE
    cR
    ctcl
    cfv
    wbr
    #
    cE
    cR
    cB
    csn
    #
    vf
    cv
    #
    cun
    cima
    #
    @2
    wss
    #
    vf
    cab
    cint
    wcel
    #
    @4
    cE
    @2
    wcel
    #
    wi
    #
    vf
    wal
    @2
    cR
    whe
    #
    cB
    va
    cv
    #
    cR
    wbr
    #
    va
    vf
    wel
    #
    wi
    #
    va
    wal
    #
    @6
    wi
    wi
    #
    vf
    wal
    cB
    cU
    wcel
    cE
    cV
    wcel
    cR
    cW
    wcel
    @0
    @5
    wb
    frege76.b
    frege76.e
    frege76.r
    cR
    cU
    vf
    cV
    cW
    cB
    cE
    brtrclfv2
    mp3an
    @4
    vf
    cE
    cE
    cV
    frege76.e
    elexi
    elintab
    @7
    @14
    vf
    @7
    @8
    @13
    wa
    #
    @6
    wi
    @14
    @4
    @15
    @6
    @4
    cR
    @2
    cima
    #
    @2
    wss
    #
    cR
    @1
    cima
    #
    @2
    wss
    #
    wa
    #
    @15
    @4
    @16
    @18
    cun
    #
    @2
    wss
    @20
    @3
    @21
    @2
    @3
    @18
    @16
    cR
    @1
    @2
    imaundi
    equncomi
    sseq1i
    @16
    @18
    @2
    unss
    bitr4i
    @17
    @8
    @19
    @13
    @8
    @17
    @2
    cR
    df-he
    bicomi
    @19
    @9
    @18
    wcel
    #
    @11
    wi
    #
    va
    wal
    @13
    va
    @18
    @2
    dfss2
    @23
    @12
    va
    @22
    @10
    @11
    @22
    cB
    @9
    cop
    cR
    wcel
    @10
    cR
    cB
    @9
    cB
    cU
    frege76.b
    elexi
    va
    vex
    elimasn
    cB
    @9
    cR
    df-br
    bitr4i
    imbi1i
    albii
    bitri
    anbi12i
    bitri
    imbi1i
    @8
    @13
    @6
    impexp
    bitri
    albii
    3bitrri
end
