include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cicc.mm"
include "simpllr.mm"
include "iooss1.mm"
include "sylancom.mm"
include "ioossicc.mm"
include "syl6ss.mm"
include "sslin.mm"
include "syl.mm"
include "simplll.mm"
include "simplrr.mm"
include "clt.mm"
include "df-ioo.mm"
include "df-icc.mm"
include "cv.mm"
include "xrlenlt.mm"
include "ixxdisj.mm"
include "syl3anc.mm"
include "sseqtrd.mm"
include "ss0.mm"

theorem ioodisj
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) ) /\ B <_ C ) -> ( ( A (,) B ) i^i ( C (,) D ) ) = (/) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    wa
    #
    wa
    #
    cB
    cC
    cle
    wbr
    #
    wa
    #
    cA
    cB
    cioo
    co
    #
    cC
    cD
    cioo
    co
    #
    cin
    #
    c0
    wss
    @11
    c0
    wceq
    @8
    @11
    @9
    cB
    cD
    cicc
    co
    #
    cin
    #
    c0
    @8
    @10
    @12
    wss
    @11
    @13
    wss
    @8
    @10
    cB
    cD
    cioo
    co
    #
    @12
    @6
    @7
    @1
    @10
    @14
    wss
    @0
    @1
    @5
    @7
    simpllr
    #
    cB
    cC
    cD
    iooss1
    sylancom
    cB
    cD
    ioossicc
    syl6ss
    @10
    @12
    @9
    sslin
    syl
    @8
    @0
    @1
    @4
    @13
    c0
    wceq
    @0
    @1
    @5
    @7
    simplll
    @15
    @2
    @3
    @4
    @7
    simplrr
    vx
    vy
    vz
    vw
    cA
    cB
    cD
    cicc
    clt
    clt
    cle
    cle
    cioo
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-icc
    cB
    vw
    cv
    xrlenlt
    ixxdisj
    syl3anc
    sseqtrd
    @11
    ss0
    syl
end
