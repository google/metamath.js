include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "csn.mm"
include "cun.mm"
include "unass.mm"
include "cico.mm"
include "wceq.mm"
include "snunioo.mm"
include "3expa.mm"
include "3adantl1.mm"
include "adantrl.mm"
include "uneq2d.mm"
include "cle.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "cv.mm"
include "xrlenlt.mm"
include "xrlttr.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem ioojoin
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A < B /\ B < C ) ) -> ( ( ( A (,) B ) u. { B } ) u. ( B (,) C ) ) = ( A (,) C ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    wa
    #
    cA
    cB
    cioo
    co
    #
    cB
    csn
    #
    cun
    cB
    cC
    cioo
    co
    #
    cun
    @7
    @8
    @9
    cun
    #
    cun
    #
    cA
    cC
    cioo
    co
    #
    @7
    @8
    @9
    unass
    @6
    @11
    @7
    cB
    cC
    cico
    co
    #
    cun
    @12
    @6
    @10
    @13
    @7
    @3
    @5
    @10
    @13
    wceq
    #
    @4
    @1
    @2
    @5
    @14
    @0
    @1
    @2
    @5
    @14
    cB
    cC
    snunioo
    3expa
    3adantl1
    adantrl
    uneq2d
    vx
    vy
    vz
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
    clt
    vx
    vy
    vz
    df-ioo
    #
    vx
    vy
    vz
    df-ico
    cB
    vw
    cv
    #
    xrlenlt
    @15
    @16
    cB
    cC
    xrlttr
    cA
    cB
    @16
    xrltletr
    ixxun
    eqtrd
    syl5eq
end
