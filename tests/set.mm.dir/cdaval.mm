include "wcel.mm"
include "cvv.mm"
include "ccda.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "p0ex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "snex.mm"
include "anim12i.mm"
include "unexb.mm"
include "sylib.mm"
include "cv.mm"
include "xpeq1.mm"
include "uneq1d.mm"
include "uneq2d.mm"
include "df-cda.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"
include "syl2an.mm"

theorem cdaval
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( A +c B ) = ( ( A X. { (/) } ) u. ( B X. { 1o } ) ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    ccda
    co
    cA
    c0
    csn
    #
    cxp
    #
    cB
    c1o
    csn
    #
    cxp
    #
    cun
    #
    wceq
    #
    cB
    cW
    wcel
    cA
    cV
    elex
    cB
    cW
    elex
    @0
    @1
    @6
    cvv
    wcel
    #
    @7
    @0
    @1
    wa
    @3
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    wa
    @8
    @0
    @9
    @1
    @10
    @0
    @2
    cvv
    wcel
    @9
    p0ex
    cA
    @2
    cvv
    cvv
    xpexg
    mpan2
    @1
    @4
    cvv
    wcel
    @10
    c1o
    snex
    cB
    @4
    cvv
    cvv
    xpexg
    mpan2
    anim12i
    @3
    @5
    unexb
    sylib
    vx
    vy
    cA
    cB
    cvv
    cvv
    vx
    cv
    #
    @2
    cxp
    #
    vy
    cv
    #
    @4
    cxp
    #
    cun
    @6
    ccda
    @3
    @14
    cun
    cvv
    @11
    cA
    wceq
    @12
    @3
    @14
    @11
    cA
    @2
    xpeq1
    uneq1d
    @13
    cB
    wceq
    @14
    @5
    @3
    @13
    cB
    @4
    xpeq1
    uneq2d
    vx
    vy
    df-cda
    ovmpt2g
    mpd3an3
    syl2an
end
