include "cv.mm"
include "cun.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "wo.mm"
include "elun.mm"
include "imbi1i.mm"
include "jaob.mm"
include "bitri.mm"
include "albii.mm"
include "19.26.mm"
include "df-ral.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem ralunb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A. x e. ( A u. B ) ph <-> ( A. x e. A ph /\ A. x e. B ph ) )

  proof
    vx
    cv
    #
    cA
    cB
    cun
    #
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    @0
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    @0
    cB
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    wa
    #
    wph
    vx
    @1
    wral
    wph
    vx
    cA
    wral
    #
    wph
    vx
    cB
    wral
    #
    wa
    @4
    @6
    @9
    wa
    #
    vx
    wal
    @11
    @3
    @14
    vx
    @3
    @5
    @8
    wo
    #
    wph
    wi
    @14
    @2
    @15
    wph
    @0
    cA
    cB
    elun
    imbi1i
    @5
    wph
    @8
    jaob
    bitri
    albii
    @6
    @9
    vx
    19.26
    bitri
    wph
    vx
    @1
    df-ral
    @12
    @7
    @13
    @10
    wph
    vx
    cA
    df-ral
    wph
    vx
    cB
    df-ral
    anbi12i
    3bitr4i
end
