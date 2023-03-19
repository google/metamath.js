include "cin.mm"
include "cmpt.mm"
include "clsi.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "resmpt3.mm"
include "eqcomi.mm"
include "a1i.mm"
include "fveq2d.mm"
include "cvv.mm"
include "mptexd.mm"
include "liminfresico.mm"
include "eqtrd.mm"

theorem liminfresicompt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  assume liminfresicompt.1: |- ( ph -> M e. RR )
  assume liminfresicompt.2: |- Z = ( M [,) +oo )
  assume liminfresicompt.3: |- ( ph -> A e. V )

  disjoint A x
  disjoint Z x
  disjoint k x
  assert |- ( ph -> ( liminf ` ( x e. ( A i^i Z ) |-> B ) ) = ( liminf ` ( x e. A |-> B ) ) )

  proof
    wph
    vx
    cA
    cZ
    cin
    cB
    cmpt
    #
    clsi
    cfv
    vx
    cA
    cB
    cmpt
    #
    cZ
    cres
    #
    clsi
    cfv
    @1
    clsi
    cfv
    wph
    @0
    @2
    clsi
    @0
    @2
    wceq
    wph
    @2
    @0
    vx
    cA
    cZ
    cB
    resmpt3
    eqcomi
    a1i
    fveq2d
    wph
    @1
    cM
    cvv
    cZ
    liminfresicompt.1
    liminfresicompt.2
    wph
    vx
    cA
    cB
    cV
    liminfresicompt.3
    mptexd
    liminfresico
    eqtrd
end
