include "csn.mm"
include "crab.mm"
include "wceq.mm"
include "wsbc.mm"
include "c0.mm"
include "cif.mm"
include "wo.mm"
include "rabsnifsb.mm"
include "eqeq2i.mm"
include "ifeqor.mm"
include "orcom.mm"
include "mpbi.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "mpbiri.mm"
include "sylbi.mm"

theorem rabrsn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cM: class M

  disjoint A x
  assert |- ( M = { x e. { A } | ph } -> ( M = (/) \/ M = { A } ) )

  proof
    cM
    wph
    vx
    cA
    csn
    #
    crab
    #
    wceq
    cM
    wph
    vx
    cA
    wsbc
    #
    @0
    c0
    cif
    #
    wceq
    #
    cM
    c0
    wceq
    #
    cM
    @0
    wceq
    #
    wo
    #
    @1
    @3
    cM
    wph
    vx
    cA
    rabsnifsb
    eqeq2i
    @4
    @7
    @3
    c0
    wceq
    #
    @3
    @0
    wceq
    #
    wo
    #
    @9
    @8
    wo
    @10
    @2
    @0
    c0
    ifeqor
    @9
    @8
    orcom
    mpbi
    @4
    @5
    @8
    @6
    @9
    cM
    @3
    c0
    eqeq1
    cM
    @3
    @0
    eqeq1
    orbi12d
    mpbiri
    sylbi
end
