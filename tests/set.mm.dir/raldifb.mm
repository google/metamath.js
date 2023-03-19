include "cv.mm"
include "wnel.mm"
include "wi.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "impexp.mm"
include "wn.mm"
include "df-nel.mm"
include "anbi2i.mm"
include "eldif.mm"
include "bitr4i.mm"
include "imbi1i.mm"
include "bitr3i.mm"
include "ralbii2.mm"

theorem raldifb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A. x e. A ( x e/ B -> ph ) <-> A. x e. ( A \ B ) ph )

  proof
    vx
    cv
    #
    cB
    wnel
    #
    wph
    wi
    #
    wph
    vx
    cA
    cA
    cB
    cdif
    #
    @0
    cA
    wcel
    #
    @2
    wi
    @4
    @1
    wa
    #
    wph
    wi
    @0
    @3
    wcel
    #
    wph
    wi
    @4
    @1
    wph
    impexp
    @5
    @6
    wph
    @5
    @4
    @0
    cB
    wcel
    wn
    #
    wa
    @6
    @1
    @7
    @4
    @0
    cB
    df-nel
    anbi2i
    @0
    cA
    cB
    eldif
    bitr4i
    imbi1i
    bitr3i
    ralbii2
end
