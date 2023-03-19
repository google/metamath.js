include "cref.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "refbas.mm"
include "adantr.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "refssex.mm"
include "adantlr.mm"
include "0ss.mm"
include "a1i.mm"
include "reximdva0.mm"
include "wb.mm"
include "elsni.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "syl.mm"
include "adantl.mm"
include "mpbird.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "refrel.mm"
include "brrelexi.mm"
include "p0ex.mm"
include "unexg.mm"
include "sylancl.mm"
include "uniun.mm"
include "0ex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtrri.mm"
include "isref.mm"
include "mpbir2and.mm"

theorem refun0
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( A Ref B /\ B =/= (/) ) -> ( A u. { (/) } ) Ref B )

  proof
    cA
    cB
    cref
    wbr
    #
    cB
    c0
    wne
    #
    wa
    #
    cA
    c0
    csn
    #
    cun
    #
    cB
    cref
    wbr
    #
    cB
    cuni
    #
    cA
    cuni
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cB
    wrex
    #
    vx
    @4
    wral
    #
    @0
    @8
    @1
    cA
    cB
    @7
    @6
    @7
    eqid
    @6
    eqid
    #
    refbas
    adantr
    @2
    @12
    vx
    @4
    @9
    @4
    wcel
    @2
    @9
    cA
    wcel
    #
    @9
    @3
    wcel
    #
    wo
    @12
    @9
    cA
    @3
    elun
    @2
    @15
    @12
    @16
    @0
    @15
    @12
    @1
    vy
    cA
    cB
    @9
    refssex
    adantlr
    @2
    @16
    wa
    @12
    c0
    @10
    wss
    #
    vy
    cB
    wrex
    #
    @2
    @18
    @16
    @0
    @17
    vy
    cB
    @17
    @0
    @10
    cB
    wcel
    wa
    @10
    0ss
    a1i
    reximdva0
    adantr
    @16
    @12
    @18
    wb
    #
    @2
    @16
    @9
    c0
    wceq
    #
    @19
    @9
    c0
    elsni
    @20
    @11
    @17
    vy
    cB
    @9
    c0
    @10
    sseq1
    rexbidv
    syl
    adantl
    mpbird
    jaodan
    sylan2b
    ralrimiva
    @0
    @5
    @8
    @13
    wa
    wb
    #
    @1
    @0
    @4
    cvv
    wcel
    #
    @21
    @0
    cA
    cvv
    wcel
    @3
    cvv
    wcel
    @22
    cA
    cB
    cref
    refrel
    brrelexi
    p0ex
    cA
    @3
    cvv
    cvv
    unexg
    sylancl
    vx
    vy
    @4
    cB
    cvv
    @7
    @6
    @4
    cuni
    @7
    @3
    cuni
    #
    cun
    @7
    c0
    cun
    @7
    cA
    @3
    uniun
    @23
    c0
    @7
    c0
    0ex
    unisn
    uneq2i
    @7
    un0
    3eqtrri
    @14
    isref
    syl
    adantr
    mpbir2and
end
