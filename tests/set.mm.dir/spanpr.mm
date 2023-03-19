include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cph.mm"
include "cpr.mm"
include "cv.mm"
include "csh.mm"
include "spansnsh.mm"
include "shscl.mm"
include "syl2an.mm"
include "adantr.mm"
include "anim12i.mm"
include "spansnid.mm"
include "shsva.mm"
include "sylc.mm"
include "simpr.mm"
include "elspansn3.mm"
include "syl3anc.mm"
include "ex.mm"
include "ssrdv.mm"
include "cun.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "spanun.mm"
include "syl5req.mm"
include "sseqtrd.mm"

theorem spanpr
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( span ` { ( A +h B ) } ) C_ ( span ` { A , B } ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    cva
    co
    #
    csn
    cspn
    cfv
    #
    cA
    csn
    #
    cspn
    cfv
    #
    cB
    csn
    #
    cspn
    cfv
    #
    cph
    co
    #
    cA
    cB
    cpr
    #
    cspn
    cfv
    #
    @2
    vx
    @4
    @9
    @2
    vx
    cv
    #
    @4
    wcel
    #
    @12
    @9
    wcel
    #
    @2
    @13
    wa
    @9
    csh
    wcel
    #
    @3
    @9
    wcel
    #
    @13
    @14
    @2
    @15
    @13
    @0
    @6
    csh
    wcel
    #
    @8
    csh
    wcel
    #
    @15
    @1
    cA
    spansnsh
    #
    cB
    spansnsh
    #
    @6
    @8
    shscl
    syl2an
    adantr
    @2
    @16
    @13
    @2
    @17
    @18
    wa
    cA
    @6
    wcel
    #
    cB
    @8
    wcel
    #
    wa
    @16
    @0
    @17
    @1
    @18
    @19
    @20
    anim12i
    @0
    @21
    @1
    @22
    cA
    spansnid
    cB
    spansnid
    anim12i
    @6
    @8
    cA
    cB
    shsva
    sylc
    adantr
    @2
    @13
    simpr
    @9
    @3
    @12
    elspansn3
    syl3anc
    ex
    ssrdv
    @2
    @11
    @5
    @7
    cun
    #
    cspn
    cfv
    #
    @9
    @10
    @23
    cspn
    cA
    cB
    df-pr
    fveq2i
    @0
    @5
    chil
    wss
    @7
    chil
    wss
    @24
    @9
    wceq
    @1
    cA
    chil
    snssi
    cB
    chil
    snssi
    @5
    @7
    spanun
    syl2an
    syl5req
    sseqtrd
end
