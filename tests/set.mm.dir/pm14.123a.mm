include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "wcel.mm"
include "wsbc.mm"
include "2albiim.mm"
include "2sbc6g.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem pm14.123a
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A w
  disjoint w z
  disjoint A z
  disjoint B w
  disjoint B z
  assert |- ( ( A e. V /\ B e. W ) -> ( A. z A. w ( ph <-> ( z = A /\ w = B ) ) <-> ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\ [. A / z ]. [. B / w ]. ph ) ) )

  proof
    wph
    vz
    cv
    cA
    wceq
    vw
    cv
    cB
    wceq
    wa
    #
    wb
    vw
    wal
    vz
    wal
    wph
    @0
    wi
    vw
    wal
    vz
    wal
    #
    @0
    wph
    wi
    vw
    wal
    vz
    wal
    #
    wa
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    @1
    wph
    vw
    cB
    wsbc
    vz
    cA
    wsbc
    #
    wa
    wph
    @0
    vz
    vw
    2albiim
    @3
    @2
    @4
    @1
    wph
    vz
    vw
    cA
    cB
    cV
    cW
    2sbc6g
    anbi2d
    syl5bb
end
