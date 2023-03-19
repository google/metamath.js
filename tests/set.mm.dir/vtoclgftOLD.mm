include "wcel.mm"
include "wnfc.mm"
include "wnf.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "elex.mm"
include "w3a.mm"
include "wex.mm"
include "elisset.mm"
include "3ad2ant3.mm"
include "nfnfc1.mm"
include "nfcvd.mm"
include "id.mm"
include "nfeqd.mm"
include "eqeq1.mm"
include "a1i.mm"
include "cbvexd.mm"
include "ad2antrr.mm"
include "3adant3.mm"
include "mpbid.mm"
include "biimp.mm"
include "imim2i.mm"
include "com23.mm"
include "imp.mm"
include "alanimi.mm"
include "3ad2ant2.mm"
include "simp1r.mm"
include "19.23t.mm"
include "syl.mm"
include "mpd.mm"
include "syl3an3.mm"

theorem vtoclgftOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vz: setvar z


  assert |- ( ( ( F/_ x A /\ F/ x ps ) /\ ( A. x ( x = A -> ( ph <-> ps ) ) /\ A. x ph ) /\ A e. V ) -> ps )

  proof
    cA
    cV
    wcel
    vx
    cA
    wnfc
    #
    wps
    vx
    wnf
    #
    wa
    #
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    wph
    vx
    wal
    wa
    #
    cA
    cvv
    wcel
    #
    wps
    cA
    cV
    elex
    @2
    @7
    @8
    w3a
    #
    @4
    vx
    wex
    #
    wps
    @9
    vz
    cv
    #
    cA
    wceq
    #
    vz
    wex
    #
    @10
    @8
    @2
    @13
    @7
    vz
    cA
    cvv
    elisset
    3ad2ant3
    @2
    @7
    @13
    @10
    wb
    #
    @8
    @0
    @14
    @1
    @7
    @0
    @12
    @4
    vz
    vx
    vx
    cA
    nfnfc1
    @0
    vx
    @11
    cA
    @0
    vx
    @11
    nfcvd
    @0
    id
    nfeqd
    @11
    @3
    wceq
    @12
    @4
    wb
    wi
    @0
    @11
    @3
    cA
    eqeq1
    a1i
    cbvexd
    ad2antrr
    3adant3
    mpbid
    @9
    @4
    wps
    wi
    #
    vx
    wal
    #
    @10
    wps
    wi
    #
    @7
    @2
    @16
    @8
    @6
    wph
    @15
    vx
    @6
    wph
    @15
    @6
    @4
    wph
    wps
    @5
    wph
    wps
    wi
    @4
    wph
    wps
    biimp
    imim2i
    com23
    imp
    alanimi
    3ad2ant2
    @9
    @1
    @16
    @17
    wb
    @0
    @1
    @7
    @8
    simp1r
    @4
    wps
    vx
    19.23t
    syl
    mpbid
    mpd
    syl3an3
end
