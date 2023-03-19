include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cxne.mm"
include "clsi.mm"
include "cxr.mm"
include "wcel.mm"
include "cvv.mm"
include "ovex.mm"
include "inex2.mm"
include "mptex.mm"
include "limsupcl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "xnegnegd.mm"
include "eqcomd.mm"
include "eqid.mm"
include "limsupresicompt.mm"
include "cv.mm"
include "wa.mm"
include "xnegcld.mm"
include "liminfval3.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "xnegeqd.mm"
include "3eqtr4d.mm"

theorem limsupval4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cM: class M
  let cV: class V
  let vk: setvar k
  assume limsupval4.x: |- F/ x ph
  assume limsupval4.a: |- ( ph -> A e. V )
  assume limsupval4.m: |- ( ph -> M e. RR )
  assume limsupval4.b: |- ( ( ph /\ x e. ( A i^i ( M [,) +oo ) ) ) -> B e. RR* )

  disjoint A x
  disjoint M x
  disjoint k x
  assert |- ( ph -> ( limsup ` ( x e. A |-> B ) ) = -e ( liminf ` ( x e. A |-> -e B ) ) )

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
    #
    clsp
    cfv
    #
    @3
    cxne
    #
    cxne
    #
    vx
    cA
    cB
    cmpt
    clsp
    cfv
    vx
    cA
    cB
    cxne
    #
    cmpt
    clsi
    cfv
    #
    cxne
    wph
    @5
    @3
    wph
    @3
    @3
    cxr
    wcel
    #
    wph
    @2
    cvv
    wcel
    @8
    vx
    @1
    cB
    @0
    cA
    cM
    cpnf
    cico
    ovex
    inex2
    mptex
    @2
    cvv
    limsupcl
    ax-mp
    a1i
    xnegnegd
    eqcomd
    wph
    vx
    cA
    cB
    cM
    cV
    @0
    limsupval4.a
    limsupval4.m
    @0
    eqid
    #
    limsupresicompt
    wph
    @7
    @4
    wph
    @7
    vx
    cA
    @6
    cxne
    #
    cmpt
    clsp
    cfv
    #
    cxne
    @4
    wph
    vx
    cA
    @6
    cM
    cV
    limsupval4.x
    limsupval4.a
    limsupval4.m
    wph
    vx
    cv
    @1
    wcel
    wa
    #
    cB
    limsupval4.b
    xnegcld
    liminfval3
    wph
    @11
    @3
    wph
    @11
    vx
    @1
    @10
    cmpt
    #
    clsp
    cfv
    @3
    wph
    vx
    cA
    @10
    cM
    cV
    @0
    limsupval4.a
    limsupval4.m
    @9
    limsupresicompt
    wph
    @13
    @2
    clsp
    wph
    vx
    @1
    @10
    cB
    limsupval4.x
    @12
    cB
    limsupval4.b
    xnegnegd
    mpteq2da
    fveq2d
    eqtrd
    xnegeqd
    eqtrd
    xnegeqd
    3eqtr4d
end
