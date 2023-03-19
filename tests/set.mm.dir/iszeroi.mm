include "ccat.mm"
include "wcel.mm"
include "czeroo.mm"
include "cfv.mm"
include "wa.mm"
include "cbs.mm"
include "cinito.mm"
include "ctermo.mm"
include "cin.mm"
include "chom.mm"
include "id.mm"
include "eqid.mm"
include "zerooval.mm"
include "eleq2d.mm"
include "elin.mm"
include "initoo.mm"
include "adantrd.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "imp.mm"
include "simpl.mm"
include "simpr.mm"
include "iszeroo.mm"
include "biimpd.mm"
include "impancom.mm"
include "jcai.mm"

theorem iszeroi
  let cC: class C
  let cO: class O


  assert |- ( ( C e. Cat /\ O e. ( ZeroO ` C ) ) -> ( O e. ( Base ` C ) /\ ( O e. ( InitO ` C ) /\ O e. ( TermO ` C ) ) ) )

  proof
    cC
    ccat
    wcel
    #
    cO
    cC
    czeroo
    cfv
    #
    wcel
    #
    wa
    cO
    cC
    cbs
    cfv
    #
    wcel
    #
    cO
    cC
    cinito
    cfv
    #
    wcel
    #
    cO
    cC
    ctermo
    cfv
    #
    wcel
    #
    wa
    #
    @0
    @2
    @4
    @0
    @2
    cO
    @5
    @7
    cin
    #
    wcel
    #
    @4
    @0
    @1
    @10
    cO
    @0
    @3
    cC
    cC
    chom
    cfv
    #
    @0
    id
    @3
    eqid
    #
    @12
    eqid
    #
    zerooval
    eleq2d
    @11
    @9
    @0
    @4
    cO
    @5
    @7
    elin
    @0
    @6
    @4
    @8
    cC
    cO
    initoo
    adantrd
    syl5bi
    sylbid
    imp
    @0
    @4
    @2
    @9
    @0
    @4
    wa
    #
    @2
    @9
    @15
    @3
    cC
    @12
    cO
    @13
    @14
    @0
    @4
    simpl
    @0
    @4
    simpr
    iszeroo
    biimpd
    impancom
    jcai
end
