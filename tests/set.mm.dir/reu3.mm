include "wreu.mm"
include "wrex.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "reurex.mm"
include "wb.mm"
include "reu6.mm"
include "biimp.mm"
include "ralimi.mm"
include "reximi.mm"
include "sylbi.mm"
include "jca.mm"
include "wex.mm"
include "rexex.mm"
include "anim2i.mm"
include "cv.mm"
include "wcel.mm"
include "weu.mm"
include "wal.mm"
include "eu3v.mm"
include "df-reu.mm"
include "df-rex.mm"
include "df-ral.mm"
include "impexp.mm"
include "albii.mm"
include "bitr4i.mm"
include "exbii.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "sylibr.mm"
include "impbii.mm"

theorem reu3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let wps: wff ps

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint ps x
  assert |- ( E! x e. A ph <-> ( E. x e. A ph /\ E. y e. A A. x e. A ( ph -> x = y ) ) )

  proof
    wph
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    cA
    wral
    #
    vy
    cA
    wrex
    #
    wa
    #
    @0
    @1
    @5
    wph
    vx
    cA
    reurex
    @0
    wph
    @2
    wb
    #
    vx
    cA
    wral
    #
    vy
    cA
    wrex
    @5
    wph
    vx
    vy
    cA
    reu6
    @8
    @4
    vy
    cA
    @7
    @3
    vx
    cA
    wph
    @2
    biimp
    ralimi
    reximi
    sylbi
    jca
    @6
    @1
    @4
    vy
    wex
    #
    wa
    #
    @0
    @5
    @9
    @1
    @4
    vy
    cA
    rexex
    anim2i
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    weu
    @12
    vx
    wex
    #
    @12
    @2
    wi
    #
    vx
    wal
    #
    vy
    wex
    #
    wa
    @0
    @10
    @12
    vx
    vy
    eu3v
    wph
    vx
    cA
    df-reu
    @1
    @13
    @9
    @16
    wph
    vx
    cA
    df-rex
    @4
    @15
    vy
    @4
    @11
    @3
    wi
    #
    vx
    wal
    @15
    @3
    vx
    cA
    df-ral
    @14
    @17
    vx
    @11
    wph
    @2
    impexp
    albii
    bitr4i
    exbii
    anbi12i
    3bitr4i
    sylibr
    impbii
end
