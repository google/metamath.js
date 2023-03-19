include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "2reu2.mm"
include "pm5.32i.mm"
include "nfcv.mm"
include "nfreu1.mm"
include "nfreu.mm"
include "reuan.mm"
include "ancom.mm"
include "reubii.mm"
include "nfre1.mm"
include "3bitri.mm"
include "3bitr4ri.mm"
include "2reu7.mm"
include "3bitr3ri.mm"

theorem 2reu8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( E! x e. A E! y e. B ( E. x e. A ph /\ E. y e. B ph ) <-> E! x e. A E! y e. B ( E! x e. A ph /\ E. y e. B ph ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wreu
    #
    vy
    cB
    wreu
    #
    wa
    #
    @1
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wa
    @2
    @0
    wa
    #
    vy
    cB
    wreu
    #
    vx
    cA
    wreu
    #
    @5
    @0
    wa
    vy
    cB
    wreu
    vx
    cA
    wreu
    @1
    @3
    @6
    wph
    vy
    vx
    cB
    cA
    2reu2
    pm5.32i
    @3
    @0
    wa
    #
    vx
    cA
    wreu
    @3
    @1
    wa
    @9
    @4
    @3
    @0
    vx
    cA
    @2
    vx
    vy
    cB
    vx
    cB
    nfcv
    wph
    vx
    cA
    nfreu1
    nfreu
    reuan
    @8
    @10
    vx
    cA
    @8
    @0
    @2
    wa
    #
    vy
    cB
    wreu
    @0
    @3
    wa
    @10
    @7
    @11
    vy
    cB
    @2
    @0
    ancom
    reubii
    @0
    @2
    vy
    cB
    wph
    vy
    cB
    nfre1
    reuan
    @0
    @3
    ancom
    3bitri
    reubii
    @1
    @3
    ancom
    3bitr4ri
    wph
    vx
    vy
    cA
    cB
    2reu7
    3bitr3ri
end
