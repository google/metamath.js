include "wn.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wal.mm"
include "wrex.mm"
include "raln.mm"
include "wex.mm"
include "alnex.mm"
include "df-rex.mm"
include "xchbinxr.mm"
include "bitri.mm"

theorem ralnex
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A -. ph <-> -. E. x e. A ph )

  proof
    wph
    wn
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    wn
    vx
    wal
    #
    wph
    vx
    cA
    wrex
    #
    wn
    wph
    vx
    cA
    raln
    @1
    @0
    vx
    wex
    @2
    @0
    vx
    alnex
    wph
    vx
    cA
    df-rex
    xchbinxr
    bitri
end
