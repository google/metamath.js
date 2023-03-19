include "wn.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "df-ral.mm"
include "imnang.mm"
include "bitri.mm"

theorem raln
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A -. ph <-> A. x -. ( x e. A /\ ph ) )

  proof
    wph
    wn
    #
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    #
    @0
    wi
    vx
    wal
    @1
    wph
    wa
    wn
    vx
    wal
    @0
    vx
    cA
    df-ral
    @1
    wph
    vx
    imnang
    bitri
end
