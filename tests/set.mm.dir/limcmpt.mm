include "cmpt.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "ccnp.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfif.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "cbvmpt.mm"
include "cc.mm"
include "eqid.mm"
include "fmptd.mm"
include "ellimc.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "pm5.61.mm"
include "simplbi.mm"
include "sylanb.mm"
include "adantl.mm"
include "sylan2.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "anassrs.mm"
include "ifeq2da.mm"
include "mpteq2dva.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem limcmpt
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let vy: setvar y
  assume limcmpt.a: |- ( ph -> A C_ CC )
  assume limcmpt.b: |- ( ph -> B e. CC )
  assume limcmpt.f: |- ( ( ph /\ z e. A ) -> D e. CC )
  assume limcmpt.j: |- J = ( K |`t ( A u. { B } ) )
  assume limcmpt.k: |- K = ( TopOpen ` CCfld )

  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint K y
  assert |- ( ph -> ( C e. ( ( z e. A |-> D ) limCC B ) <-> ( z e. ( A u. { B } ) |-> if ( z = B , C , D ) ) e. ( ( J CnP K ) ` B ) ) )

  proof
    wph
    cC
    vz
    cA
    cD
    cmpt
    #
    cB
    climc
    co
    wcel
    vz
    cA
    cB
    csn
    #
    cun
    #
    vz
    cv
    #
    cB
    wceq
    #
    cC
    @3
    @0
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cJ
    cK
    ccnp
    co
    cfv
    #
    wcel
    vz
    @2
    @4
    cC
    cD
    cif
    #
    cmpt
    #
    @8
    wcel
    wph
    vy
    cA
    cB
    cC
    @0
    @7
    cJ
    cK
    limcmpt.j
    limcmpt.k
    vz
    vy
    @2
    @6
    vy
    cv
    #
    cB
    wceq
    #
    cC
    @11
    @0
    cfv
    #
    cif
    vy
    @6
    nfcv
    @12
    vz
    cC
    @13
    @12
    vz
    nfv
    vz
    cC
    nfcv
    vz
    cA
    cD
    @11
    nffvmpt1
    nfif
    @3
    @11
    wceq
    @4
    @12
    @5
    @13
    cC
    @3
    @11
    cB
    eqeq1
    @3
    @11
    @0
    fveq2
    ifbieq2d
    cbvmpt
    wph
    vz
    cA
    cD
    cc
    @0
    limcmpt.f
    @0
    eqid
    #
    fmptd
    limcmpt.a
    limcmpt.b
    ellimc
    wph
    @7
    @10
    @8
    wph
    vz
    @2
    @6
    @9
    wph
    @3
    @2
    wcel
    #
    wa
    @4
    @5
    cD
    cC
    wph
    @15
    @4
    wn
    #
    @5
    cD
    wceq
    #
    wph
    @15
    @16
    wa
    #
    wa
    @3
    cA
    wcel
    #
    cD
    cc
    wcel
    #
    @17
    @18
    @19
    wph
    @15
    @19
    @4
    wo
    #
    @16
    @19
    @15
    @19
    @3
    @1
    wcel
    #
    wo
    @21
    @3
    cA
    @1
    elun
    @22
    @4
    @19
    vz
    cB
    velsn
    orbi2i
    bitri
    @21
    @16
    wa
    @19
    @16
    @19
    @4
    pm5.61
    simplbi
    sylanb
    #
    adantl
    @18
    wph
    @19
    @20
    @23
    limcmpt.f
    sylan2
    vz
    cA
    cD
    cc
    @0
    @14
    fvmpt2
    syl2anc
    anassrs
    ifeq2da
    mpteq2dva
    eleq1d
    bitrd
end
