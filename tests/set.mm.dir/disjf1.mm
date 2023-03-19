include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wf1.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "ralrimiva.mm"
include "c0.mm"
include "wn.mm"
include "cin.mm"
include "inidm.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ineq2.mm"
include "ad2antlr.mm"
include "wdisj.mm"
include "wne.mm"
include "cbvdisj.mm"
include "sylib.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "neqne.mm"
include "adantl.mm"
include "csbeq1.mm"
include "disji2.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "nfne.mm"
include "neeq1d.mm"
include "adantrr.mm"
include "ad2antrr.mm"
include "neneqd.mm"
include "condan.mm"
include "ex.mm"
include "ralrimivva.mm"
include "jca.mm"
include "cmpt.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "f1mpt.mm"
include "sylibr.mm"

theorem disjf1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume disjf1.xph: |- F/ x ph
  assume disjf1.f: |- F = ( x e. A |-> B )
  assume disjf1.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume disjf1.n0: |- ( ( ph /\ x e. A ) -> B =/= (/) )
  assume disjf1.dj: |- ( ph -> Disj_ x e. A B )

  disjoint A x
  disjoint V x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F z
  disjoint V y
  disjoint V z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> F : A -1-1-> V )

  proof
    wph
    vx
    vy
    cv
    #
    cB
    csb
    #
    cV
    wcel
    #
    vy
    cA
    wral
    #
    @1
    vx
    vz
    cv
    #
    cB
    csb
    #
    wceq
    #
    @0
    @4
    wceq
    #
    wi
    #
    vz
    cA
    wral
    vy
    cA
    wral
    #
    wa
    cA
    cV
    cF
    wf1
    wph
    @3
    @9
    wph
    @2
    vy
    cA
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cV
    wcel
    #
    wi
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @2
    wi
    vx
    vy
    @15
    @2
    vx
    wph
    @14
    vx
    disjf1.xph
    @14
    vx
    nfv
    nfan
    #
    vx
    @1
    cV
    vx
    @0
    cB
    nfcsb1v
    #
    vx
    cV
    nfcv
    nfel
    nfim
    @10
    @0
    wceq
    #
    @12
    @15
    @13
    @2
    @18
    @11
    @14
    wph
    @10
    @0
    cA
    eleq1
    anbi2d
    #
    @18
    cB
    @1
    cV
    vx
    @0
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    disjf1.b
    chvar
    ralrimiva
    wph
    @8
    vy
    vz
    cA
    cA
    wph
    @14
    @4
    cA
    wcel
    #
    wa
    #
    wa
    #
    @6
    @7
    @23
    @6
    wa
    #
    @7
    @1
    c0
    wceq
    @24
    @7
    wn
    #
    wa
    #
    @1
    @1
    @1
    cin
    #
    @1
    @5
    cin
    #
    c0
    @1
    @27
    wceq
    @26
    @27
    @1
    @1
    inidm
    eqcomi
    a1i
    @6
    @27
    @28
    wceq
    @23
    @25
    @1
    @5
    @1
    ineq2
    ad2antlr
    @26
    vw
    cA
    vx
    vw
    cv
    #
    cB
    csb
    #
    wdisj
    #
    @22
    @0
    @4
    wne
    #
    @28
    c0
    wceq
    wph
    @31
    @22
    @6
    @25
    wph
    vx
    cA
    cB
    wdisj
    @31
    disjf1.dj
    vx
    vw
    cA
    cB
    @30
    vw
    cB
    nfcv
    vx
    @29
    cB
    nfcsb1v
    vx
    @29
    cB
    csbeq1a
    cbvdisj
    sylib
    ad3antrrr
    wph
    @22
    @6
    @25
    simpllr
    @25
    @32
    @24
    @0
    @4
    neqne
    adantl
    vw
    cA
    @30
    @1
    @5
    @0
    @4
    vx
    @29
    @0
    cB
    csbeq1
    vx
    @29
    @4
    cB
    csbeq1
    disji2
    syl3anc
    3eqtrd
    @26
    @1
    c0
    @23
    @1
    c0
    wne
    #
    @6
    @25
    wph
    @14
    @33
    @21
    @12
    cB
    c0
    wne
    #
    wi
    @15
    @33
    wi
    vx
    vy
    @15
    @33
    vx
    @16
    vx
    @1
    c0
    @17
    vx
    c0
    nfcv
    nfne
    nfim
    @18
    @12
    @15
    @34
    @33
    @19
    @18
    cB
    @1
    c0
    @20
    neeq1d
    imbi12d
    disjf1.n0
    chvar
    adantrr
    ad2antrr
    neneqd
    condan
    ex
    ralrimivva
    jca
    vy
    vz
    cA
    cV
    @1
    @5
    cF
    cF
    vx
    cA
    cB
    cmpt
    vy
    cA
    @1
    cmpt
    disjf1.f
    vx
    vy
    cA
    cB
    @1
    vy
    cB
    nfcv
    @17
    @20
    cbvmpt
    eqtri
    vx
    @0
    @4
    cB
    csbeq1
    f1mpt
    sylibr
end
