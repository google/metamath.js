include "cima.mm"
include "wss.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wral.mm"
include "wb.mm"
include "cres.mm"
include "df-ima.mm"
include "reseq1i.mm"
include "resmpt3.mm"
include "eqtri.mm"
include "rneqi.mm"
include "sseq1i.mm"
include "a1i.mm"
include "eqid.mm"
include "rnmptssbi.mm"
include "bitrd.mm"

theorem imassmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume imassmpt.1: |- F/ x ph
  assume imassmpt.2: |- ( ( ph /\ x e. ( A i^i C ) ) -> B e. V )
  assume imassmpt.3: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( ph -> ( ( F " C ) C_ D <-> A. x e. ( A i^i C ) B e. D ) )

  proof
    wph
    cF
    cC
    cima
    #
    cD
    wss
    #
    vx
    cA
    cC
    cin
    #
    cB
    cmpt
    #
    crn
    #
    cD
    wss
    #
    cB
    cD
    wcel
    vx
    @2
    wral
    @1
    @5
    wb
    wph
    @0
    @4
    cD
    @0
    cF
    cC
    cres
    #
    crn
    @4
    cF
    cC
    df-ima
    @6
    @3
    @6
    vx
    cA
    cB
    cmpt
    #
    cC
    cres
    @3
    cF
    @7
    cC
    imassmpt.3
    reseq1i
    vx
    cA
    cC
    cB
    resmpt3
    eqtri
    rneqi
    eqtri
    sseq1i
    a1i
    wph
    vx
    @2
    cB
    cD
    @3
    cV
    imassmpt.1
    @3
    eqid
    imassmpt.2
    rnmptssbi
    bitrd
end
