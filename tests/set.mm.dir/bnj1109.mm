include "wceq.mm"
include "wi.mm"
include "wne.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "ex.mm"
include "a1i.mm"
include "ax-gen.mm"
include "impexp.mm"
include "exbii.mm"
include "mpbi.mm"
include "exintr.mm"
include "mp2.mm"
include "exancom.mm"
include "wn.mm"
include "df-ne.mm"
include "imbi1i.mm"
include "pm2.61.mm"
include "imp.mm"
include "sylan2b.mm"
include "bnj101.mm"

theorem bnj1109
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bnj1109.1: |- E. x ( ( A =/= B /\ ph ) -> ps )
  assume bnj1109.2: |- ( ( A = B /\ ph ) -> ps )


  assert |- E. x ( ph -> ps )

  proof
    cA
    cB
    wceq
    #
    wph
    wps
    wi
    #
    wi
    #
    cA
    cB
    wne
    #
    @1
    wi
    #
    wa
    #
    @1
    vx
    @4
    @2
    wa
    vx
    wex
    #
    @5
    vx
    wex
    @4
    @2
    wi
    #
    vx
    wal
    @4
    vx
    wex
    #
    @6
    @7
    vx
    @2
    @4
    @0
    wph
    wps
    bnj1109.2
    ex
    a1i
    ax-gen
    @3
    wph
    wa
    wps
    wi
    #
    vx
    wex
    @8
    bnj1109.1
    @9
    @4
    vx
    @3
    wph
    wps
    impexp
    exbii
    mpbi
    @4
    @2
    vx
    exintr
    mp2
    @4
    @2
    vx
    exancom
    mpbi
    @4
    @2
    @0
    wn
    #
    @1
    wi
    #
    @1
    @3
    @10
    @1
    cA
    cB
    df-ne
    imbi1i
    @2
    @11
    @1
    @0
    @1
    pm2.61
    imp
    sylan2b
    bnj101
end
