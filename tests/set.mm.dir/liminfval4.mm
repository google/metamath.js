include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cmpt.mm"
include "clsi.mm"
include "cfv.mm"
include "cneg.mm"
include "clsp.mm"
include "cxne.mm"
include "cvv.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "ssexd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "rexrd.mm"
include "liminfvalxrmpt.mm"
include "rexnegd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "xnegeqd.mm"
include "eqtrd.mm"
include "eqid.mm"
include "liminfresicompt.mm"
include "eqcomd.mm"
include "limsupresicompt.mm"
include "3eqtr4d.mm"

theorem liminfval4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cM: class M
  let cV: class V
  let vk: setvar k
  assume liminfval4.x: |- F/ x ph
  assume liminfval4.a: |- ( ph -> A e. V )
  assume liminfval4.m: |- ( ph -> M e. RR )
  assume liminfval4.b: |- ( ( ph /\ x e. ( A i^i ( M [,) +oo ) ) ) -> B e. RR )

  disjoint A x
  disjoint M x
  disjoint k x
  assert |- ( ph -> ( liminf ` ( x e. A |-> B ) ) = -e ( limsup ` ( x e. A |-> -u B ) ) )

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
    cneg
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    #
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
    @2
    vx
    @1
    cB
    cxne
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    @6
    wph
    vx
    @1
    cB
    cvv
    liminfval4.x
    wph
    @1
    cA
    cV
    liminfval4.a
    @1
    cA
    wss
    wph
    cA
    @0
    inss1
    a1i
    ssexd
    wph
    vx
    cv
    @1
    wcel
    wa
    #
    cB
    liminfval4.b
    rexrd
    liminfvalxrmpt
    wph
    @11
    @5
    wph
    @10
    @4
    clsp
    wph
    vx
    @1
    @9
    @3
    liminfval4.x
    @12
    cB
    liminfval4.b
    rexnegd
    mpteq2da
    fveq2d
    xnegeqd
    eqtrd
    wph
    @2
    @7
    wph
    vx
    cA
    cB
    cM
    cV
    @0
    liminfval4.m
    @0
    eqid
    #
    liminfval4.a
    liminfresicompt
    eqcomd
    wph
    @8
    @5
    wph
    vx
    cA
    @3
    cM
    cV
    @0
    liminfval4.a
    liminfval4.m
    @13
    limsupresicompt
    xnegeqd
    3eqtr4d
end
