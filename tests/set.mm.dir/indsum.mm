include "cv.mm"
include "cind.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "wcel.mm"
include "cc.mm"
include "sselda.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cr.mm"
include "pr01ssre.mm"
include "cfn.mm"
include "wss.mm"
include "wf.mm"
include "indf.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "recnd.mm"
include "mulcld.mm"
include "syldan.mm"
include "cdif.mm"
include "wceq.mm"
include "adantr.mm"
include "simpr.mm"
include "ind0.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "difssd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "fsumss.mm"
include "ind1.mm"
include "mulid2d.mm"
include "sumeq2dv.mm"
include "eqtr3d.mm"

theorem indsum
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cO: class O
  assume indsum.1: |- ( ph -> O e. Fin )
  assume indsum.2: |- ( ph -> A C_ O )
  assume indsum.3: |- ( ( ph /\ x e. O ) -> B e. CC )

  disjoint A x
  disjoint O x
  disjoint ph x
  assert |- ( ph -> sum_ x e. O ( ( ( ( _Ind ` O ) ` A ) ` x ) x. B ) = sum_ x e. A B )

  proof
    wph
    cA
    vx
    cv
    #
    cA
    cO
    cind
    cfv
    cfv
    #
    cfv
    #
    cB
    cmul
    co
    #
    vx
    csu
    cO
    @3
    vx
    csu
    cA
    cB
    vx
    csu
    wph
    cA
    cO
    @3
    vx
    indsum.2
    wph
    @0
    cA
    wcel
    #
    @0
    cO
    wcel
    #
    @3
    cc
    wcel
    wph
    cA
    cO
    @0
    indsum.2
    sselda
    #
    wph
    @5
    wa
    #
    @2
    cB
    @7
    @2
    @7
    cc0
    c1
    cpr
    #
    cr
    @2
    pr01ssre
    wph
    cO
    @8
    @0
    @1
    wph
    cO
    cfn
    wcel
    #
    cA
    cO
    wss
    #
    cO
    @8
    @1
    wf
    indsum.1
    indsum.2
    cA
    cO
    cfn
    indf
    syl2anc
    ffvelrnda
    sseldi
    recnd
    indsum.3
    mulcld
    syldan
    wph
    @0
    cO
    cA
    cdif
    #
    wcel
    #
    wa
    #
    @3
    cc0
    cB
    cmul
    co
    #
    cc0
    @13
    @2
    cc0
    cB
    cmul
    @13
    @9
    @10
    @12
    @2
    cc0
    wceq
    wph
    @9
    @12
    indsum.1
    adantr
    wph
    @10
    @12
    indsum.2
    adantr
    wph
    @12
    simpr
    cA
    cO
    cfn
    @0
    ind0
    syl3anc
    oveq1d
    wph
    @12
    @5
    @14
    cc0
    wceq
    wph
    @11
    cO
    @0
    wph
    cO
    cA
    difssd
    sselda
    @7
    cB
    indsum.3
    mul02d
    syldan
    eqtrd
    indsum.1
    fsumss
    wph
    cA
    @3
    cB
    vx
    wph
    @4
    wa
    #
    @3
    c1
    cB
    cmul
    co
    #
    cB
    @15
    @2
    c1
    cB
    cmul
    @15
    @9
    @10
    @4
    @2
    c1
    wceq
    wph
    @9
    @4
    indsum.1
    adantr
    wph
    @10
    @4
    indsum.2
    adantr
    wph
    @4
    simpr
    cA
    cO
    cfn
    @0
    ind1
    syl3anc
    oveq1d
    wph
    @4
    @5
    @16
    cB
    wceq
    @6
    @7
    cB
    indsum.3
    mulid2d
    syldan
    eqtrd
    sumeq2dv
    eqtr3d
end
