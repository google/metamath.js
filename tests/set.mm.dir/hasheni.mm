include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "wb.mm"
include "enfii.mm"
include "ancoms.mm"
include "hashen.mm"
include "sylancom.mm"
include "mpbird.mm"
include "wn.mm"
include "cpnf.mm"
include "cvv.mm"
include "relen.mm"
include "brrelexi.mm"
include "adantr.mm"
include "enfi.mm"
include "notbid.mm"
include "biimpar.mm"
include "hashinf.mm"
include "syl2anc.mm"
include "brrelex2i.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem hasheni
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cN: class N


  assert |- ( A ~~ B -> ( # ` A ) = ( # ` B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cB
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
    wceq
    #
    @0
    @1
    wa
    @4
    @0
    @0
    @1
    simpl
    @0
    @1
    cA
    cfn
    wcel
    #
    @4
    @0
    wb
    @1
    @0
    @5
    cA
    cB
    enfii
    ancoms
    cA
    cB
    hashen
    sylancom
    mpbird
    @0
    @1
    wn
    #
    wa
    #
    @2
    cpnf
    @3
    @7
    cA
    cvv
    wcel
    #
    @5
    wn
    #
    @2
    cpnf
    wceq
    @0
    @8
    @6
    cA
    cB
    cen
    relen
    brrelexi
    adantr
    @0
    @9
    @6
    @0
    @5
    @1
    cA
    cB
    enfi
    notbid
    biimpar
    cA
    cvv
    hashinf
    syl2anc
    @0
    cB
    cvv
    wcel
    @6
    @3
    cpnf
    wceq
    cA
    cB
    cen
    relen
    brrelex2i
    cB
    cvv
    hashinf
    sylan
    eqtr4d
    pm2.61dan
end
