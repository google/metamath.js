include "wrex.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wmo.mm"
include "wrmo.mm"
include "wreu.mm"
include "wb.mm"
include "nfra1.mm"
include "nfmo.mm"
include "wcel.mm"
include "wal.mm"
include "rsp.mm"
include "com3l.mm"
include "alrimdv.mm"
include "mo2icl.mm"
include "syl6.mm"
include "rexlimi.mm"
include "mormo.mm"
include "reu5.mm"
include "rbaib.mm"
include "3syl.mm"

theorem reusv1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint x y
  assert |- ( E. y e. B ph -> ( E! x e. A A. y e. B ( ph -> x = C ) <-> E. x e. A A. y e. B ( ph -> x = C ) ) )

  proof
    wph
    vy
    cB
    wrex
    wph
    vx
    cv
    cC
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    wmo
    #
    @2
    vx
    cA
    wrmo
    #
    @2
    vx
    cA
    wreu
    #
    @2
    vx
    cA
    wrex
    #
    wb
    wph
    @3
    vy
    cB
    @2
    vy
    vx
    @1
    vy
    cB
    nfra1
    nfmo
    vy
    cv
    cB
    wcel
    #
    wph
    @2
    @0
    wi
    #
    vx
    wal
    @3
    @7
    wph
    @8
    vx
    @2
    @7
    wph
    @0
    @1
    vy
    cB
    rsp
    com3l
    alrimdv
    @2
    vx
    cC
    mo2icl
    syl6
    rexlimi
    @2
    vx
    cA
    mormo
    @5
    @6
    @4
    @2
    vx
    cA
    reu5
    rbaib
    3syl
end
