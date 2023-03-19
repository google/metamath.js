include "wsbc.mm"
include "cv.mm"
include "wcel.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "sbcbii.mm"
include "cvv.mm"
include "wb.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfxfr.mm"
include "nf3an.mm"
include "nfan.mm"
include "wceq.mm"
include "eleq1.mm"
include "fneq2.mm"
include "sbceq1a.mm"
include "syl6bbr.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "bnj252.mm"
include "3bitr4g.mm"
include "sbciegf.mm"
include "ax-mp.mm"
include "3bitri.mm"

theorem bnj919
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cD: class D
  let cP: class P
  let vn: setvar n
  let cF: class F
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj919.1: |- ( ch <-> ( n e. D /\ F Fn n /\ ph /\ ps ) )
  assume bnj919.2: |- ( ph' <-> [. P / n ]. ph )
  assume bnj919.3: |- ( ps' <-> [. P / n ]. ps )
  assume bnj919.4: |- ( ch' <-> [. P / n ]. ch )
  assume bnj919.5: |- P e. _V

  disjoint D n
  disjoint F n
  disjoint P n
  assert |- ( ch' <-> ( P e. D /\ F Fn P /\ ph' /\ ps' ) )

  proof
    bnjwchm
    wch
    vn
    cP
    wsbc
    vn
    cv
    #
    cD
    wcel
    #
    cF
    @0
    wfn
    #
    wph
    wps
    w-bnj17
    #
    vn
    cP
    wsbc
    #
    cP
    cD
    wcel
    #
    cF
    cP
    wfn
    #
    bnjwphm
    bnjwpsm
    w-bnj17
    #
    bnj919.4
    wch
    @3
    vn
    cP
    bnj919.1
    sbcbii
    cP
    cvv
    wcel
    @4
    @7
    wb
    bnj919.5
    @3
    @7
    vn
    cP
    cvv
    @7
    @5
    @6
    bnjwphm
    w3a
    #
    bnjwpsm
    wa
    vn
    @5
    @6
    bnjwphm
    bnjwpsm
    df-bnj17
    @8
    bnjwpsm
    vn
    @5
    @6
    bnjwphm
    vn
    @5
    vn
    nfv
    @6
    vn
    nfv
    bnjwphm
    wph
    vn
    cP
    wsbc
    #
    vn
    bnj919.2
    wph
    vn
    cP
    nfsbc1v
    nfxfr
    nf3an
    bnjwpsm
    wps
    vn
    cP
    wsbc
    #
    vn
    bnj919.3
    wps
    vn
    cP
    nfsbc1v
    nfxfr
    nfan
    nfxfr
    @0
    cP
    wceq
    #
    @1
    @2
    wph
    wps
    w3a
    #
    wa
    @5
    @6
    bnjwphm
    bnjwpsm
    w3a
    #
    wa
    @3
    @7
    @11
    @1
    @5
    @12
    @13
    @0
    cP
    cD
    eleq1
    @11
    @2
    @6
    wph
    bnjwphm
    wps
    bnjwpsm
    @0
    cP
    cF
    fneq2
    @11
    wph
    @9
    bnjwphm
    wph
    vn
    cP
    sbceq1a
    bnj919.2
    syl6bbr
    @11
    wps
    @10
    bnjwpsm
    wps
    vn
    cP
    sbceq1a
    bnj919.3
    syl6bbr
    3anbi123d
    anbi12d
    @1
    @2
    wph
    wps
    bnj252
    @5
    @6
    bnjwphm
    bnjwpsm
    bnj252
    3bitr4g
    sbciegf
    ax-mp
    3bitri
end
