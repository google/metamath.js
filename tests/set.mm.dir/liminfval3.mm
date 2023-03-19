include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cmpt.mm"
include "clsi.mm"
include "cfv.mm"
include "cxne.mm"
include "clsp.mm"
include "cvv.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "ssexd.mm"
include "liminfvalxrmpt.mm"
include "eqid.mm"
include "liminfresicompt.mm"
include "eqcomd.mm"
include "limsupresicompt.mm"
include "xnegeqd.mm"
include "3eqtr4d.mm"

theorem liminfval3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cM: class M
  let cV: class V
  let vk: setvar k
  assume liminfval3.x: |- F/ x ph
  assume liminfval3.a: |- ( ph -> A e. V )
  assume liminfval3.m: |- ( ph -> M e. RR )
  assume liminfval3.b: |- ( ( ph /\ x e. ( A i^i ( M [,) +oo ) ) ) -> B e. RR* )

  disjoint A x
  disjoint M x
  disjoint k x
  assert |- ( ph -> ( liminf ` ( x e. A |-> B ) ) = -e ( limsup ` ( x e. A |-> -e B ) ) )

  proof
    wph
    vx
    cA
    cM
    cpnf
    cico
    co
    #
    cin
    #
    cB
    cmpt
    clsi
    cfv
    #
    vx
    @1
    cB
    cxne
    #
    cmpt
    clsp
    cfv
    #
    cxne
    vx
    cA
    cB
    cmpt
    clsi
    cfv
    #
    vx
    cA
    @3
    cmpt
    clsp
    cfv
    #
    cxne
    wph
    vx
    @1
    cB
    cvv
    liminfval3.x
    wph
    @1
    cA
    cV
    liminfval3.a
    @1
    cA
    wss
    wph
    cA
    @0
    inss1
    a1i
    ssexd
    liminfval3.b
    liminfvalxrmpt
    wph
    @2
    @5
    wph
    vx
    cA
    cB
    cM
    cV
    @0
    liminfval3.m
    @0
    eqid
    #
    liminfval3.a
    liminfresicompt
    eqcomd
    wph
    @6
    @4
    wph
    vx
    cA
    @3
    cM
    cV
    @0
    liminfval3.a
    liminfval3.m
    @7
    limsupresicompt
    xnegeqd
    3eqtr4d
end
