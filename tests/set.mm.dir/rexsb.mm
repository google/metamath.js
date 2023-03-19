include "weq.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "nfa1.mm"
include "ax12v.mm"
include "sp.mm"
include "com12.mm"
include "impbid.mm"
include "cbvrex.mm"

theorem rexsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint k x
  assert |- ( E. x e. A ph <-> E. y e. A A. x ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    vx
    vy
    cA
    wph
    vy
    nfv
    @1
    vx
    nfa1
    @0
    wph
    @2
    wph
    vx
    vy
    ax12v
    @2
    @0
    wph
    @1
    vx
    sp
    com12
    impbid
    cbvrex
end
