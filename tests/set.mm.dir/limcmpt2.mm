include "csn.mm"
include "cdif.mm"
include "cmpt.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "crest.mm"
include "ccnp.mm"
include "cfv.mm"
include "cc.mm"
include "ssdifssd.mm"
include "sseldd.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "sylan2b.mm"
include "eqid.mm"
include "limcmpt.mm"
include "undif1.mm"
include "wss.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleq12d.mm"
include "bitrd.mm"

theorem limcmpt2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  assume limcmpt2.a: |- ( ph -> A C_ CC )
  assume limcmpt2.b: |- ( ph -> B e. A )
  assume limcmpt2.f: |- ( ( ph /\ ( z e. A /\ z =/= B ) ) -> D e. CC )
  assume limcmpt2.j: |- J = ( K |`t A )
  assume limcmpt2.k: |- K = ( TopOpen ` CCfld )

  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  assert |- ( ph -> ( C e. ( ( z e. ( A \ { B } ) |-> D ) limCC B ) <-> ( z e. A |-> if ( z = B , C , D ) ) e. ( ( J CnP K ) ` B ) ) )

  proof
    wph
    cC
    vz
    cA
    cB
    csn
    #
    cdif
    #
    cD
    cmpt
    cB
    climc
    co
    wcel
    vz
    @1
    @0
    cun
    #
    vz
    cv
    #
    cB
    wceq
    cC
    cD
    cif
    #
    cmpt
    #
    cB
    cK
    @2
    crest
    co
    #
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    vz
    cA
    @4
    cmpt
    #
    cB
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    wph
    vz
    @1
    cB
    cC
    cD
    @6
    cK
    wph
    cA
    cc
    @0
    limcmpt2.a
    ssdifssd
    wph
    cA
    cc
    cB
    limcmpt2.a
    limcmpt2.b
    sseldd
    @3
    @1
    wcel
    wph
    @3
    cA
    wcel
    @3
    cB
    wne
    wa
    cD
    cc
    wcel
    @3
    cA
    cB
    eldifsn
    limcmpt2.f
    sylan2b
    @6
    eqid
    limcmpt2.k
    limcmpt
    wph
    @5
    @9
    @8
    @11
    wph
    vz
    @2
    cA
    @4
    wph
    @2
    cA
    @0
    cun
    #
    cA
    cA
    @0
    undif1
    wph
    @0
    cA
    wss
    @12
    cA
    wceq
    wph
    cB
    cA
    limcmpt2.b
    snssd
    @0
    cA
    ssequn2
    sylib
    syl5eq
    #
    mpteq1d
    wph
    cB
    @7
    @10
    wph
    @6
    cJ
    cK
    ccnp
    wph
    @6
    cK
    cA
    crest
    co
    cJ
    wph
    @2
    cA
    cK
    crest
    @13
    oveq2d
    limcmpt2.j
    syl6eqr
    oveq1d
    fveq1d
    eleq12d
    bitrd
end
