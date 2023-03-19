include "wn.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "df-ral.mm"
include "wa.mm"
include "wex.mm"
include "alinexa.mm"
include "df-rex.mm"
include "xchbinxr.mm"
include "bitri.mm"

theorem ralnexOLD
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A -. ph <-> -. E. x e. A ph )

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
    #
    wph
    vx
    cA
    wrex
    #
    wn
    @0
    vx
    cA
    df-ral
    @2
    @1
    wph
    wa
    vx
    wex
    @3
    @1
    wph
    vx
    alinexa
    wph
    vx
    cA
    df-rex
    xchbinxr
    bitri
end
