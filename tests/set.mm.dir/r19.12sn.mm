include "wcel.mm"
include "wral.mm"
include "wsbc.mm"
include "csn.mm"
include "wrex.mm"
include "sbcralg.mm"
include "rexsns.mm"
include "ralbii.mm"
include "3bitr4g.mm"

theorem r19.12sn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  assert |- ( A e. V -> ( E. x e. { A } A. y e. B ph <-> A. y e. B E. x e. { A } ph ) )

  proof
    cA
    cV
    wcel
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    wral
    @0
    vx
    cA
    csn
    #
    wrex
    wph
    vx
    @2
    wrex
    #
    vy
    cB
    wral
    wph
    vx
    vy
    cA
    cB
    cV
    sbcralg
    @0
    vx
    cA
    rexsns
    @3
    @1
    vy
    cB
    wph
    vx
    cA
    rexsns
    ralbii
    3bitr4g
end
