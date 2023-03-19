include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "wex.mm"
include "wb.mm"
include "2sbc5g.mm"
include "adantr.mm"
include "nfa1.mm"
include "nfa2.mm"
include "simpr.mm"
include "2sp.mm"
include "ancrd.mm"
include "impbid2.mm"
include "exbid.mm"
include "adantl.mm"
include "bitr3d.mm"
include "pm5.32da.mm"

theorem pm14.123b
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
  assert |- ( ( A e. V /\ B e. W ) -> ( ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\ [. A / z ]. [. B / w ]. ph ) <-> ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\ E. z E. w ph ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
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
    wi
    #
    vw
    wal
    #
    vz
    wal
    #
    wph
    vw
    cB
    wsbc
    vz
    cA
    wsbc
    #
    wph
    vw
    wex
    #
    vz
    wex
    #
    @0
    @4
    wa
    @1
    wph
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    @5
    @7
    @0
    @10
    @5
    wb
    @4
    wph
    vz
    vw
    cA
    cB
    cV
    cW
    2sbc5g
    adantr
    @4
    @10
    @7
    wb
    @0
    @4
    @9
    @6
    vz
    @3
    vz
    nfa1
    @4
    @8
    wph
    vw
    @2
    vw
    vz
    nfa2
    @4
    @8
    wph
    @1
    wph
    simpr
    @4
    wph
    @1
    @2
    vz
    vw
    2sp
    ancrd
    impbid2
    exbid
    exbid
    adantl
    bitr3d
    pm5.32da
end
