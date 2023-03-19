include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wral.mm"
include "wrex.mm"
include "exnal.mm"
include "xchbinxr.mm"
include "alinexa.mm"
include "con2bii.mm"
include "exbii.mm"
include "ralnex2.mm"
include "3bitr4ri.mm"

theorem r2exlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r2exlem.1: |- ( A. x e. A A. y e. B -. ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> -. ph ) )


  assert |- ( E. x e. A E. y e. B ph <-> E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) )

  proof
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    wph
    wn
    #
    wi
    vy
    wal
    #
    wn
    #
    vx
    wex
    #
    @1
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wn
    @0
    wph
    wa
    vy
    wex
    #
    vx
    wex
    wph
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    @4
    @2
    vx
    wal
    @5
    @2
    vx
    exnal
    r2exlem.1
    xchbinxr
    @6
    @3
    vx
    @2
    @6
    @0
    wph
    vy
    alinexa
    con2bii
    exbii
    @5
    @7
    wph
    vx
    vy
    cA
    cB
    ralnex2
    con2bii
    3bitr4ri
end
