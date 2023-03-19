include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "wnel.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "velsn.mm"
include "nnel.mm"
include "nne.mm"
include "3bitr4ri.mm"
include "con4bii.mm"
include "imbi1i.mm"
include "ralbii.mm"
include "raldifb.mm"
include "bitri.mm"

theorem raldifsnb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cY: class Y

  disjoint Y x
  assert |- ( A. x e. A ( x =/= Y -> ph ) <-> A. x e. ( A \ { Y } ) ph )

  proof
    vx
    cv
    #
    cY
    wne
    #
    wph
    wi
    #
    vx
    cA
    wral
    @0
    cY
    csn
    #
    wnel
    #
    wph
    wi
    #
    vx
    cA
    wral
    wph
    vx
    cA
    @3
    cdif
    wral
    @2
    @5
    vx
    cA
    @1
    @4
    wph
    @1
    @4
    @0
    @3
    wcel
    @0
    cY
    wceq
    @4
    wn
    @1
    wn
    vx
    cY
    velsn
    @0
    @3
    nnel
    @0
    cY
    nne
    3bitr4ri
    con4bii
    imbi1i
    ralbii
    wph
    vx
    cA
    @3
    raldifb
    bitri
end
