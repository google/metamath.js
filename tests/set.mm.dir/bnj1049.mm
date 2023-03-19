include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "w-bnj17.mm"
include "wa.mm"
include "imbi2i.mm"
include "impexp.mm"
include "bitr4i.mm"
include "cfv.mm"
include "simplbi.mm"
include "bnj708.mm"
include "pm4.71ri.mm"
include "bicomi.mm"
include "imbi1i.mm"
include "bitri.mm"
include "albii.mm"

theorem bnj1049
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  assume bnj1049.1: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1049.2: |- ( et <-> ( ( th /\ ta /\ ch /\ ze ) -> z e. B ) )


  assert |- ( A. i e. n et <-> A. i et )

  proof
    wet
    vi
    vn
    cv
    #
    wral
    vi
    cv
    #
    @0
    wcel
    #
    wet
    wi
    #
    vi
    wal
    wet
    vi
    wal
    wet
    vi
    @0
    df-ral
    @3
    wet
    vi
    @3
    wth
    wta
    wch
    wze
    w-bnj17
    #
    vz
    cv
    #
    cB
    wcel
    #
    wi
    #
    wet
    @3
    @2
    @4
    wa
    #
    @6
    wi
    #
    @7
    @3
    @2
    @7
    wi
    @9
    wet
    @7
    @2
    bnj1049.2
    imbi2i
    @2
    @4
    @6
    impexp
    bitr4i
    @8
    @4
    @6
    @4
    @8
    @4
    @2
    wth
    wta
    wch
    wze
    @2
    wze
    @2
    @5
    @1
    vf
    cv
    cfv
    wcel
    bnj1049.1
    simplbi
    bnj708
    pm4.71ri
    bicomi
    imbi1i
    bitri
    bnj1049.2
    bitr4i
    albii
    bitri
end
