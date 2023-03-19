include "wel.mm"
include "wb.mm"
include "weq.mm"
include "wi.mm"
include "wex.mm"
include "wn.mm"
include "wal.mm"
include "axextnd.mm"
include "wa.mm"
include "dfbi2.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "exbii.mm"
include "df-ex.mm"
include "mpbi.mm"

theorem axextprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. A. x -. ( ( x e. y -> x e. z ) -> ( ( x e. z -> x e. y ) -> y = z ) )

  proof
    vx
    vy
    wel
    #
    vx
    vz
    wel
    #
    wb
    #
    vy
    vz
    weq
    #
    wi
    #
    vx
    wex
    #
    @0
    @1
    wi
    #
    @1
    @0
    wi
    #
    @3
    wi
    wi
    #
    wn
    vx
    wal
    wn
    #
    vx
    vy
    vz
    axextnd
    @5
    @8
    vx
    wex
    @9
    @4
    @8
    vx
    @4
    @6
    @7
    wa
    #
    @3
    wi
    @8
    @2
    @10
    @3
    @0
    @1
    dfbi2
    imbi1i
    @6
    @7
    @3
    impexp
    bitri
    exbii
    @8
    vx
    df-ex
    bitri
    mpbi
end
