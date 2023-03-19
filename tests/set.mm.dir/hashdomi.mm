include "cdom.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wa.mm"
include "simpl.mm"
include "cvv.mm"
include "wb.mm"
include "simpr.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "adantr.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "wn.mm"
include "cpnf.mm"
include "cxr.mm"
include "pnfxr.mm"
include "pnfge.mm"
include "mp1i.mm"
include "wceq.mm"
include "brrelexi.mm"
include "hashinf.mm"
include "sylan.mm"
include "domfi.mm"
include "stoic1b.mm"
include "3brtr4d.mm"
include "pm2.61dan.mm"

theorem hashdomi
  let cA: class A
  let cB: class B


  assert |- ( A ~<_ B -> ( # ` A ) <_ ( # ` B ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    cA
    cfn
    wcel
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @4
    @0
    @0
    @1
    simpl
    @5
    @1
    cB
    cvv
    wcel
    #
    @4
    @0
    wb
    @0
    @1
    simpr
    @0
    @6
    @1
    cA
    cB
    cdom
    reldom
    brrelex2i
    #
    adantr
    cA
    cB
    cvv
    hashdom
    syl2anc
    mpbird
    @0
    @1
    wn
    #
    wa
    #
    cpnf
    cpnf
    @2
    @3
    cle
    cpnf
    cxr
    wcel
    cpnf
    cpnf
    cle
    wbr
    @9
    pnfxr
    cpnf
    pnfge
    mp1i
    @0
    cA
    cvv
    wcel
    @8
    @2
    cpnf
    wceq
    cA
    cB
    cdom
    reldom
    brrelexi
    cA
    cvv
    hashinf
    sylan
    @9
    @6
    cB
    cfn
    wcel
    #
    wn
    @3
    cpnf
    wceq
    @0
    @6
    @8
    @7
    adantr
    @10
    @0
    @1
    cB
    cA
    domfi
    stoic1b
    cB
    cvv
    hashinf
    syl2anc
    3brtr4d
    pm2.61dan
end
