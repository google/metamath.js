include "cmpt.mm"
include "cv.mm"
include "csb.mm"
include "cibl.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wral.mm"
include "simpr.mm"
include "nfv.mm"
include "nfan.mm"
include "adantlr.mm"
include "ex.mm"
include "ralrimi.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "wceq.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "syl5eqel.mm"
include "iblsplit.mm"

theorem iblsplitf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vy: setvar y
  let vk: setvar k
  assume iblsplitf.X: |- F/ x ph
  assume iblsplitf.vol: |- ( ph -> ( vol* ` ( A i^i B ) ) = 0 )
  assume iblsplitf.u: |- ( ph -> U = ( A u. B ) )
  assume iblsplitf.c: |- ( ( ph /\ x e. U ) -> C e. CC )
  assume iblsplitf.a: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume iblsplitf.b: |- ( ph -> ( x e. B |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint U x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint U y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( x e. U |-> C ) e. L^1 )

  proof
    wph
    vx
    cU
    cC
    cmpt
    vy
    cU
    vx
    vy
    cv
    #
    cC
    csb
    #
    cmpt
    cibl
    vx
    vy
    cU
    cC
    @1
    vy
    cC
    nfcv
    #
    vx
    @0
    cC
    nfcsb1v
    #
    vx
    @0
    cC
    csbeq1a
    #
    cbvmpt
    wph
    vy
    cA
    cB
    @1
    cU
    iblsplitf.vol
    iblsplitf.u
    wph
    @0
    cU
    wcel
    #
    wa
    #
    @5
    cC
    cc
    wcel
    #
    vx
    cU
    wral
    @1
    cc
    wcel
    wph
    @5
    simpr
    @6
    @7
    vx
    cU
    wph
    @5
    vx
    iblsplitf.X
    @5
    vx
    nfv
    nfan
    @6
    vx
    cv
    #
    cU
    wcel
    #
    @7
    wph
    @9
    @7
    @5
    iblsplitf.c
    adantlr
    ex
    ralrimi
    vx
    @0
    cU
    cC
    cc
    rspcsbela
    syl2anc
    wph
    vy
    cA
    @1
    cmpt
    vx
    cA
    cC
    cmpt
    cibl
    vy
    vx
    cA
    @1
    cC
    @3
    @2
    @0
    @8
    wceq
    cC
    @1
    cC
    @1
    wceq
    vx
    vy
    @4
    equcoms
    eqcomd
    #
    cbvmpt
    iblsplitf.a
    syl5eqel
    wph
    vy
    cB
    @1
    cmpt
    vx
    cB
    cC
    cmpt
    cibl
    vy
    vx
    cB
    @1
    cC
    @3
    @2
    @10
    cbvmpt
    iblsplitf.b
    syl5eqel
    iblsplit
    syl5eqel
end
