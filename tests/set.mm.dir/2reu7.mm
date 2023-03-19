include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfreu.mm"
include "reuan.mm"
include "ancom.mm"
include "reubii.mm"
include "3bitri.mm"
include "3bitr4ri.mm"

theorem 2reu7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <-> E! x e. A E! y e. B ( E. x e. A ph /\ E. y e. B ph ) )

  proof
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wph
    vy
    cB
    wrex
    #
    wa
    #
    vx
    cA
    wreu
    @1
    @2
    vx
    cA
    wreu
    #
    wa
    @0
    @2
    wa
    #
    vy
    cB
    wreu
    #
    vx
    cA
    wreu
    @4
    @1
    wa
    @1
    @2
    vx
    cA
    @0
    vx
    vy
    cB
    vx
    cB
    nfcv
    wph
    vx
    cA
    nfre1
    nfreu
    reuan
    @6
    @3
    vx
    cA
    @6
    @2
    @0
    wa
    #
    vy
    cB
    wreu
    @2
    @1
    wa
    @3
    @5
    @7
    vy
    cB
    @0
    @2
    ancom
    reubii
    @2
    @0
    vy
    cB
    wph
    vy
    cB
    nfre1
    reuan
    @2
    @1
    ancom
    3bitri
    reubii
    @4
    @1
    ancom
    3bitr4ri
end
