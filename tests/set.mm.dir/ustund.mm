include "cun.mm"
include "cxp.mm"
include "cin.mm"
include "ccom.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "xpco.mm"
include "syl.mm"
include "wss.mm"
include "xpundir.mm"
include "xpindi.mm"
include "inss1.mm"
include "syl5ss.mm"
include "syl5eqss.mm"
include "inss2.mm"
include "unssd.mm"
include "coss2.mm"
include "xpundi.mm"
include "xpindir.mm"
include "coss1.mm"
include "sstrd.mm"
include "eqsstr3d.mm"

theorem ustund
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  assume ustund.1: |- ( ph -> ( A X. A ) C_ V )
  assume ustund.2: |- ( ph -> ( B X. B ) C_ V )
  assume ustund.3: |- ( ph -> ( A i^i B ) =/= (/) )


  assert |- ( ph -> ( ( A u. B ) X. ( A u. B ) ) C_ ( V o. V ) )

  proof
    wph
    cA
    cB
    cun
    #
    @0
    cxp
    #
    cA
    cB
    cin
    #
    @0
    cxp
    #
    @0
    @2
    cxp
    #
    ccom
    #
    cV
    cV
    ccom
    #
    wph
    @2
    c0
    wne
    @5
    @1
    wceq
    ustund.3
    @0
    @2
    @0
    xpco
    syl
    wph
    @5
    @3
    cV
    ccom
    #
    @6
    wph
    @4
    cV
    wss
    @5
    @7
    wss
    wph
    @4
    cA
    @2
    cxp
    #
    cB
    @2
    cxp
    #
    cun
    cV
    cA
    cB
    @2
    xpundir
    wph
    @8
    @9
    cV
    wph
    @8
    cA
    cA
    cxp
    #
    cA
    cB
    cxp
    #
    cin
    #
    cV
    cA
    cA
    cB
    xpindi
    wph
    @12
    @10
    cV
    @10
    @11
    inss1
    ustund.1
    syl5ss
    syl5eqss
    wph
    @9
    cB
    cA
    cxp
    #
    cB
    cB
    cxp
    #
    cin
    #
    cV
    cB
    cA
    cB
    xpindi
    wph
    @15
    @14
    cV
    @13
    @14
    inss2
    ustund.2
    syl5ss
    syl5eqss
    unssd
    syl5eqss
    @4
    cV
    @3
    coss2
    syl
    wph
    @3
    cV
    wss
    @7
    @6
    wss
    wph
    @3
    @2
    cA
    cxp
    #
    @2
    cB
    cxp
    #
    cun
    cV
    @2
    cA
    cB
    xpundi
    wph
    @16
    @17
    cV
    wph
    @16
    @10
    @13
    cin
    #
    cV
    cA
    cB
    cA
    xpindir
    wph
    @18
    @10
    cV
    @10
    @13
    inss1
    ustund.1
    syl5ss
    syl5eqss
    wph
    @17
    @11
    @14
    cin
    #
    cV
    cA
    cB
    cB
    xpindir
    wph
    @19
    @14
    cV
    @11
    @14
    inss2
    ustund.2
    syl5ss
    syl5eqss
    unssd
    syl5eqss
    @3
    cV
    cV
    coss1
    syl
    sstrd
    eqsstr3d
end
