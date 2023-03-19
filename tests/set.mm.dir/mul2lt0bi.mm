include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wo.mm"
include "cle.mm"
include "wn.mm"
include "remulcld.mm"
include "0red.mm"
include "ltnled.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "mulge0d.mm"
include "ex.mm"
include "con3d.mm"
include "sylbid.mm"
include "ianor.mm"
include "syl6ib.mm"
include "orbi12d.mm"
include "sylibrd.mm"
include "imp.mm"
include "simpr.mm"
include "mul2lt0llt0.mm"
include "jca.mm"
include "mul2lt0rlt0.mm"
include "orim12d.mm"
include "mpd.mm"
include "elrpd.mm"
include "ltmul1dd.mm"
include "recnd.mm"
include "mul02d.mm"
include "breqtrd.mm"
include "ltmul2dd.mm"
include "mul01d.mm"
include "jaodan.mm"
include "impbida.mm"

theorem mul2lt0bi
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mul2lt0.1: |- ( ph -> A e. RR )
  assume mul2lt0.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( ( A x. B ) < 0 <-> ( ( A < 0 /\ 0 < B ) \/ ( 0 < A /\ B < 0 ) ) ) )

  proof
    wph
    cA
    cB
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    cA
    cc0
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    cB
    cc0
    clt
    wbr
    #
    wa
    #
    wo
    #
    wph
    @1
    wa
    #
    @2
    @6
    wo
    #
    @8
    wph
    @1
    @10
    wph
    @1
    cc0
    cA
    cle
    wbr
    #
    wn
    #
    cc0
    cB
    cle
    wbr
    #
    wn
    #
    wo
    #
    @10
    wph
    @1
    @11
    @13
    wa
    #
    wn
    #
    @15
    wph
    @1
    cc0
    @0
    cle
    wbr
    #
    wn
    @17
    wph
    @0
    cc0
    wph
    cA
    cB
    mul2lt0.1
    mul2lt0.2
    remulcld
    wph
    0red
    #
    ltnled
    wph
    @16
    @18
    wph
    @16
    @18
    wph
    @16
    wa
    cA
    cB
    wph
    cA
    cr
    wcel
    #
    @16
    mul2lt0.1
    adantr
    wph
    cB
    cr
    wcel
    #
    @16
    mul2lt0.2
    adantr
    wph
    @11
    @13
    simprl
    wph
    @11
    @13
    simprr
    mulge0d
    ex
    con3d
    sylbid
    @11
    @13
    ianor
    syl6ib
    wph
    @2
    @12
    @6
    @14
    wph
    cA
    cc0
    mul2lt0.1
    @19
    ltnled
    wph
    cB
    cc0
    mul2lt0.2
    @19
    ltnled
    orbi12d
    sylibrd
    imp
    @9
    @2
    @4
    @6
    @7
    @9
    @2
    @4
    @9
    @2
    wa
    @2
    @3
    @9
    @2
    simpr
    @9
    cA
    cB
    wph
    @20
    @1
    mul2lt0.1
    adantr
    #
    wph
    @21
    @1
    mul2lt0.2
    adantr
    #
    wph
    @1
    simpr
    #
    mul2lt0llt0
    jca
    ex
    @9
    @6
    @7
    @9
    @6
    wa
    @5
    @6
    @9
    cA
    cB
    @22
    @23
    @24
    mul2lt0rlt0
    @9
    @6
    simpr
    jca
    ex
    orim12d
    mpd
    wph
    @4
    @1
    @7
    wph
    @4
    wa
    #
    @0
    cc0
    cB
    cmul
    co
    cc0
    clt
    @25
    cA
    cc0
    cB
    wph
    @20
    @4
    mul2lt0.1
    adantr
    @25
    0red
    @25
    cB
    wph
    @21
    @4
    mul2lt0.2
    adantr
    #
    wph
    @2
    @3
    simprr
    elrpd
    wph
    @2
    @3
    simprl
    ltmul1dd
    @25
    cB
    @25
    cB
    @26
    recnd
    mul02d
    breqtrd
    wph
    @7
    wa
    #
    @0
    cA
    cc0
    cmul
    co
    cc0
    clt
    @27
    cB
    cc0
    cA
    wph
    @21
    @7
    mul2lt0.2
    adantr
    @27
    0red
    @27
    cA
    wph
    @20
    @7
    mul2lt0.1
    adantr
    #
    wph
    @5
    @6
    simprl
    elrpd
    wph
    @5
    @6
    simprr
    ltmul2dd
    @27
    cA
    @27
    cA
    @28
    recnd
    mul01d
    breqtrd
    jaodan
    impbida
end
