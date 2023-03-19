include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "ex.mm"
include "alrimi.mm"
include "wcel.mm"
include "wnfc.mm"
include "wb.mm"
include "csbiebt.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem csbiedf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume csbiedf.1: |- F/ x ph
  assume csbiedf.2: |- ( ph -> F/_ x C )
  assume csbiedf.3: |- ( ph -> A e. V )
  assume csbiedf.4: |- ( ( ph /\ x = A ) -> B = C )

  disjoint A x
  assert |- ( ph -> [_ A / x ]_ B = C )

  proof
    wph
    vx
    cv
    cA
    wceq
    #
    cB
    cC
    wceq
    #
    wi
    #
    vx
    wal
    #
    vx
    cA
    cB
    csb
    cC
    wceq
    #
    wph
    @2
    vx
    csbiedf.1
    wph
    @0
    @1
    csbiedf.4
    ex
    alrimi
    wph
    cA
    cV
    wcel
    vx
    cC
    wnfc
    @3
    @4
    wb
    csbiedf.3
    csbiedf.2
    vx
    cA
    cB
    cC
    cV
    csbiebt
    syl2anc
    mpbid
end
