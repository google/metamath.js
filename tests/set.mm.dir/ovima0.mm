include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "cima.mm"
include "csn.mm"
include "cun.mm"
include "simpr.mm"
include "ssun2.mm"
include "0ex.mm"
include "snid.mm"
include "sselii.mm"
include "syl6eqel.mm"
include "wn.mm"
include "ssun1.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "opelxpi.mm"
include "eqeq1i.mm"
include "notbii.mm"
include "biimpi.mm"
include "eliman0.mm"
include "syl2an.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "pm2.61dan.mm"

theorem ovima0
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. A /\ Y e. B ) -> ( X R Y ) e. ( ( R " ( A X. B ) ) u. { (/) } ) )

  proof
    cX
    cA
    wcel
    cY
    cB
    wcel
    wa
    #
    cX
    cY
    cR
    co
    #
    c0
    wceq
    #
    @1
    cR
    cA
    cB
    cxp
    #
    cima
    #
    c0
    csn
    #
    cun
    #
    wcel
    @0
    @2
    wa
    @1
    c0
    @6
    @0
    @2
    simpr
    @5
    @6
    c0
    @5
    @4
    ssun2
    c0
    0ex
    snid
    sselii
    syl6eqel
    @0
    @2
    wn
    #
    wa
    #
    @4
    @6
    @1
    @4
    @5
    ssun1
    @8
    @1
    cX
    cY
    cop
    #
    cR
    cfv
    #
    @4
    cX
    cY
    cR
    df-ov
    #
    @0
    @9
    @3
    wcel
    @10
    c0
    wceq
    #
    wn
    #
    @10
    @4
    wcel
    @7
    cX
    cY
    cA
    cB
    opelxpi
    @7
    @13
    @2
    @12
    @1
    @10
    c0
    @11
    eqeq1i
    notbii
    biimpi
    @9
    @3
    cR
    eliman0
    syl2an
    syl5eqel
    sseldi
    pm2.61dan
end
