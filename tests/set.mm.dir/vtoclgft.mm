include "wnfc.mm"
include "wnf.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "w3a.mm"
include "wex.mm"
include "elisset.mm"
include "nfnfc1.mm"
include "nfcvd.mm"
include "id.mm"
include "nfeqd.mm"
include "weq.mm"
include "eqeq1.mm"
include "a1i.mm"
include "cbvexd.mm"
include "syl5ib.mm"
include "ad2antrr.mm"
include "3impia.mm"
include "biimp.mm"
include "imim2i.mm"
include "com23.mm"
include "imp.mm"
include "alanimi.mm"
include "19.23t.mm"
include "adantl.mm"
include "3adant3.mm"
include "mpd.mm"

theorem vtoclgft
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vz: setvar z


  assert |- ( ( ( F/_ x A /\ F/ x ps ) /\ ( A. x ( x = A -> ( ph <-> ps ) ) /\ A. x ph ) /\ A e. V ) -> ps )

  proof
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
    cV
    wcel
    #
    w3a
    @4
    vx
    wex
    #
    wps
    @2
    @7
    @8
    @9
    @0
    @8
    @9
    wi
    @1
    @7
    @8
    vz
    cv
    #
    cA
    wceq
    #
    vz
    wex
    @0
    @9
    vz
    cA
    cV
    elisset
    @0
    @11
    @4
    vz
    vx
    vx
    cA
    nfnfc1
    @0
    vx
    @10
    cA
    @0
    vx
    @10
    nfcvd
    @0
    id
    nfeqd
    vz
    vx
    weq
    @11
    @4
    wb
    wi
    @0
    @10
    @3
    cA
    eqeq1
    a1i
    cbvexd
    syl5ib
    ad2antrr
    3impia
    @2
    @7
    @9
    wps
    wi
    #
    @8
    @2
    @7
    @12
    @7
    @4
    wps
    wi
    #
    vx
    wal
    #
    @2
    @12
    @6
    wph
    @13
    vx
    @6
    wph
    @13
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
    @1
    @14
    @12
    wb
    @0
    @4
    wps
    vx
    19.23t
    adantl
    syl5ib
    imp
    3adant3
    mpd
end
