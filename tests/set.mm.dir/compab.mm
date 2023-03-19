include "cvv.mm"
include "cab.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nfdif.mm"
include "cleqf.mm"
include "abid.mm"
include "notbii.mm"
include "compel.mm"
include "3bitr4i.mm"
include "mpgbir.mm"

theorem compab
  let wph: wff ph
  let vz: setvar z


  assert |- ( _V \ { z | ph } ) = { z | -. ph }

  proof
    cvv
    wph
    vz
    cab
    #
    cdif
    #
    wph
    wn
    #
    vz
    cab
    #
    wceq
    vz
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    #
    wb
    vz
    vz
    @1
    @3
    vz
    cvv
    @0
    vz
    cvv
    nfcv
    wph
    vz
    nfab1
    nfdif
    @2
    vz
    nfab1
    cleqf
    @4
    @0
    wcel
    #
    wn
    @2
    @5
    @6
    @7
    wph
    wph
    vz
    abid
    notbii
    vz
    @0
    compel
    @2
    vz
    abid
    3bitr4i
    mpgbir
end
