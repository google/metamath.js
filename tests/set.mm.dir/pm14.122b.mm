include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "eqeq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "dfsbcq.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "wa.mm"
include "sbc5.mm"
include "nfa1.mm"
include "simpr.mm"
include "ancr.mm"
include "sps.mm"
include "impbid2.mm"
include "exbid.mm"
include "syl5bb.mm"
include "vtoclg.mm"
include "pm5.32d.mm"

theorem pm14.122b
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A e. V -> ( ( A. x ( ph -> x = A ) /\ [. A / x ]. ph ) <-> ( A. x ( ph -> x = A ) /\ E. x ph ) ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    cA
    wsbc
    #
    wph
    vx
    wex
    #
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    vy
    cv
    #
    wsbc
    #
    @5
    wb
    #
    wi
    @3
    @4
    @5
    wb
    #
    wi
    vy
    cA
    cV
    @9
    cA
    wceq
    #
    @8
    @3
    @11
    @12
    @13
    @7
    @2
    vx
    @13
    @6
    @1
    wph
    @9
    cA
    @0
    eqeq2
    imbi2d
    albidv
    @13
    @10
    @4
    @5
    wph
    vx
    @9
    cA
    dfsbcq
    bibi1d
    imbi12d
    @10
    @6
    wph
    wa
    #
    vx
    wex
    @8
    @5
    wph
    vx
    @9
    sbc5
    @8
    @14
    wph
    vx
    @7
    vx
    nfa1
    @8
    @14
    wph
    @6
    wph
    simpr
    @7
    wph
    @14
    wi
    vx
    wph
    @6
    ancr
    sps
    impbid2
    exbid
    syl5bb
    vtoclg
    pm5.32d
end
