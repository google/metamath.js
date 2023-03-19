include "wi.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "wa.mm"
include "df-ral.mm"
include "impexp.mm"
include "bicomi.mm"
include "albii.mm"
include "3bitri.mm"

theorem bnj115
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let cD: class D
  let vn: setvar n
  assume bnj115.1: |- ( et <-> A. n e. D ( ta -> th ) )


  assert |- ( et <-> A. n ( ( n e. D /\ ta ) -> th ) )

  proof
    wet
    wta
    wth
    wi
    #
    vn
    cD
    wral
    vn
    cv
    cD
    wcel
    #
    @0
    wi
    #
    vn
    wal
    @1
    wta
    wa
    wth
    wi
    #
    vn
    wal
    bnj115.1
    @0
    vn
    cD
    df-ral
    @2
    @3
    vn
    @3
    @2
    @1
    wta
    wth
    impexp
    bicomi
    albii
    3bitri
end
