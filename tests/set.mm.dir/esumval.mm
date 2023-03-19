include "cesum.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "cuni.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "ctsu.mm"
include "df-esum.mm"
include "eqid.mm"
include "nfcv.mm"
include "fmptdF.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "adantl.mm"
include "resmptf.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "xrge0tsmsd.mm"
include "unieqd.mm"
include "syl5eq.mm"
include "xrltso.mm"
include "supex.mm"
include "unisn.mm"
include "syl6eq.mm"

theorem esumval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumval.p: |- F/ k ph
  assume esumval.0: |- F/_ k A
  assume esumval.1: |- ( ph -> A e. V )
  assume esumval.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumval.3: |- ( ( ph /\ x e. ( ~P A i^i Fin ) ) -> ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. x |-> B ) ) = C )

  disjoint k x
  disjoint A x
  disjoint ph x
  disjoint B x
  assert |- ( ph -> sum* k e. A B = sup ( ran ( x e. ( ~P A i^i Fin ) |-> C ) , RR* , < ) )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    cC
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    csn
    #
    cuni
    #
    @5
    wph
    @0
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    cuni
    @7
    cA
    cB
    vk
    df-esum
    wph
    @11
    @6
    wph
    cA
    @5
    @10
    @9
    cV
    vx
    @9
    eqid
    esumval.1
    wph
    vk
    cA
    cB
    @8
    @10
    esumval.p
    esumval.0
    vk
    @8
    nfcv
    esumval.2
    @10
    eqid
    fmptdF
    wph
    cxr
    @4
    vx
    @2
    @9
    @10
    vx
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    clt
    wph
    @3
    @15
    wph
    vx
    @2
    cC
    @14
    wph
    @12
    @2
    wcel
    #
    wa
    #
    @14
    @9
    vk
    @12
    cB
    cmpt
    #
    cgsu
    co
    cC
    @17
    @13
    @18
    @9
    cgsu
    @17
    @12
    cA
    wss
    #
    @13
    @18
    wceq
    @16
    @19
    wph
    @16
    @12
    cA
    @2
    @1
    @12
    @1
    cfn
    inss1
    sseli
    elpwid
    adantl
    vk
    cA
    @12
    cB
    esumval.0
    vk
    @12
    nfcv
    resmptf
    syl
    oveq2d
    esumval.3
    eqtr2d
    mpteq2dva
    rneqd
    supeq1d
    xrge0tsmsd
    unieqd
    syl5eq
    @5
    cxr
    @4
    clt
    xrltso
    supex
    unisn
    syl6eq
end
