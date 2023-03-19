include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "cico.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "cv.mm"
include "xrlenlt.mm"
include "ixxdisj.mm"
include "adantr.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "jca.mm"

theorem joiniooico
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A < B /\ B <_ C ) ) -> ( ( ( A (,) B ) i^i ( B [,) C ) ) = (/) /\ ( ( A (,) B ) u. ( B [,) C ) ) = ( A (,) C ) ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    w3a
    #
    cA
    cB
    clt
    wbr
    cB
    cC
    cle
    wbr
    wa
    #
    wa
    cA
    cB
    cioo
    co
    #
    cB
    cC
    cico
    co
    #
    cin
    c0
    wceq
    #
    @2
    @3
    cun
    cA
    cC
    cioo
    co
    wceq
    @0
    @4
    @1
    va
    vb
    vx
    vw
    cA
    cB
    cC
    cico
    clt
    clt
    cle
    clt
    cioo
    va
    vb
    vx
    df-ioo
    #
    va
    vb
    vx
    df-ico
    #
    cB
    vw
    cv
    #
    xrlenlt
    #
    ixxdisj
    adantr
    va
    vb
    vx
    vw
    cA
    cB
    cC
    cico
    cioo
    clt
    clt
    cle
    clt
    cioo
    clt
    cle
    @5
    @6
    @8
    @5
    @7
    cB
    cC
    xrltletr
    cA
    cB
    @7
    xrltletr
    ixxun
    jca
end
