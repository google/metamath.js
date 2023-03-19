include "wrex.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "weu.mm"
include "cun.mm"
include "wreu.mm"
include "wex.mm"
include "wb.mm"
include "df-rex.mm"
include "euor2.mm"
include "sylnbi.mm"
include "df-reu.mm"
include "elun.mm"
include "anbi1i.mm"
include "andir.mm"
include "orcom.mm"
include "bitri.mm"
include "eubii.mm"
include "3bitr4g.mm"

theorem reuun2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( -. E. x e. B ph -> ( E! x e. ( A u. B ) ph <-> E! x e. A ph ) )

  proof
    wph
    vx
    cB
    wrex
    #
    wn
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    @1
    cA
    wcel
    #
    wph
    wa
    #
    wo
    #
    vx
    weu
    #
    @5
    vx
    weu
    #
    wph
    vx
    cA
    cB
    cun
    #
    wreu
    #
    wph
    vx
    cA
    wreu
    @0
    @3
    vx
    wex
    @7
    @8
    wb
    wph
    vx
    cB
    df-rex
    @3
    @5
    vx
    euor2
    sylnbi
    @10
    @1
    @9
    wcel
    #
    wph
    wa
    #
    vx
    weu
    @7
    wph
    vx
    @9
    df-reu
    @12
    @6
    vx
    @12
    @4
    @2
    wo
    #
    wph
    wa
    #
    @6
    @11
    @13
    wph
    @1
    cA
    cB
    elun
    anbi1i
    @14
    @5
    @3
    wo
    @6
    @4
    @2
    wph
    andir
    @5
    @3
    orcom
    bitri
    bitri
    eubii
    bitri
    wph
    vx
    cA
    df-reu
    3bitr4g
end
