include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "eqid.mm"
include "cv.mm"
include "wb.mm"
include "wi.mm"
include "fvex.mm"
include "eqeq2.mm"
include "breq2.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "weu.mm"
include "fneu.mm"
include "tz6.12c.mm"
include "syl.mm"
include "vtocl.mm"
include "mpbii.mm"
include "syl5ibcom.mm"
include "wfun.mm"
include "fnfun.mm"
include "funbrfv.mm"
include "adantr.mm"
include "impbid.mm"

theorem fnbrfvb
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x


  assert |- ( ( F Fn A /\ B e. A ) -> ( ( F ` B ) = C <-> B F C ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    cF
    cfv
    #
    cC
    wceq
    #
    cB
    cC
    cF
    wbr
    #
    @2
    cB
    @3
    cF
    wbr
    #
    @4
    @5
    @2
    @3
    @3
    wceq
    #
    @6
    @3
    eqid
    @2
    @3
    vx
    cv
    #
    wceq
    #
    cB
    @8
    cF
    wbr
    #
    wb
    #
    wi
    @2
    @7
    @6
    wb
    #
    wi
    vx
    @3
    cB
    cF
    fvex
    @8
    @3
    wceq
    #
    @11
    @12
    @2
    @13
    @9
    @7
    @10
    @6
    @8
    @3
    @3
    eqeq2
    @8
    @3
    cB
    cF
    breq2
    bibi12d
    imbi2d
    @2
    @10
    vx
    weu
    @11
    vx
    cA
    cB
    cF
    fneu
    vx
    cB
    cF
    tz6.12c
    syl
    vtocl
    mpbii
    @3
    cC
    cB
    cF
    breq2
    syl5ibcom
    @0
    @5
    @4
    wi
    #
    @1
    @0
    cF
    wfun
    @14
    cA
    cF
    fnfun
    cB
    cC
    cF
    funbrfv
    syl
    adantr
    impbid
end
