include "cmpt.mm"
include "cres.mm"
include "clsp.mm"
include "cfv.mm"
include "cin.mm"
include "cvv.mm"
include "mptexd.mm"
include "limsupresico.mm"
include "wceq.mm"
include "resmpt3.mm"
include "a1i.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem limsupresicompt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  assume limsupresicompt.a: |- ( ph -> A e. V )
  assume limsupresicompt.m: |- ( ph -> M e. RR )
  assume limsupresicompt.z: |- Z = ( M [,) +oo )

  disjoint A x
  disjoint Z x
  disjoint k x
  assert |- ( ph -> ( limsup ` ( x e. A |-> B ) ) = ( limsup ` ( x e. ( A i^i Z ) |-> B ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cZ
    cres
    #
    clsp
    cfv
    @0
    clsp
    cfv
    vx
    cA
    cZ
    cin
    cB
    cmpt
    #
    clsp
    cfv
    wph
    @0
    cM
    cvv
    cZ
    limsupresicompt.m
    limsupresicompt.z
    wph
    vx
    cA
    cB
    cV
    limsupresicompt.a
    mptexd
    limsupresico
    wph
    @1
    @2
    clsp
    @1
    @2
    wceq
    wph
    vx
    cA
    cZ
    cB
    resmpt3
    a1i
    fveq2d
    eqtr3d
end
