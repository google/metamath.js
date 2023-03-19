include "wral.mm"
include "wn.mm"
include "wal.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "df-ral.mm"
include "wa.mm"
include "19.26.mm"
include "wex.mm"
include "con3.mm"
include "impcom.mm"
include "alimi.mm"
include "alnex.mm"
include "sylib.mm"
include "notnotb.mm"
include "neq0.mm"
include "xchbinx.mm"
include "sylibr.mm"
include "sylbir.mm"
include "sylan2b.mm"

theorem falseral0
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A. x -. ph /\ A. x e. A ph ) -> A = (/) )

  proof
    wph
    vx
    cA
    wral
    wph
    wn
    #
    vx
    wal
    #
    vx
    cv
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    cA
    c0
    wceq
    #
    wph
    vx
    cA
    df-ral
    @1
    @4
    wa
    @0
    @3
    wa
    #
    vx
    wal
    #
    @5
    @0
    @3
    vx
    19.26
    @7
    @2
    vx
    wex
    #
    wn
    #
    @5
    @7
    @2
    wn
    #
    vx
    wal
    @9
    @6
    @10
    vx
    @3
    @0
    @10
    @2
    wph
    con3
    impcom
    alimi
    @2
    vx
    alnex
    sylib
    @5
    @5
    wn
    @8
    @5
    notnotb
    vx
    cA
    neq0
    xchbinx
    sylibr
    sylbir
    sylan2b
end
