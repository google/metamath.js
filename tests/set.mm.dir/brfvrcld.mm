include "crcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wrex.mm"
include "wo.mm"
include "dfrcl4.mm"
include "cn0.mm"
include "wss.mm"
include "wcel.mm"
include "0nn0.mm"
include "1nn0.mm"
include "prssi.mm"
include "mp2an.mm"
include "a1i.mm"
include "brmptiunrelexpd.mm"
include "wb.mm"
include "wceq.mm"
include "oveq2.mm"
include "breqd.mm"
include "rexprg.mm"
include "syl6bb.mm"

theorem brfvrcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume brfvrcld.r: |- ( ph -> R e. _V )


  assert |- ( ph -> ( A ( r* ` R ) B <-> ( A ( R ^r 0 ) B \/ A ( R ^r 1 ) B ) ) )

  proof
    wph
    cA
    cB
    cR
    crcl
    cfv
    wbr
    cA
    cB
    cR
    vn
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vn
    cc0
    c1
    cpr
    #
    wrex
    #
    cA
    cB
    cR
    cc0
    crelexp
    co
    #
    wbr
    #
    cA
    cB
    cR
    c1
    crelexp
    co
    #
    wbr
    #
    wo
    #
    wph
    cA
    cB
    crcl
    cR
    vn
    @3
    vr
    vn
    vr
    dfrcl4
    brfvrcld.r
    @3
    cn0
    wss
    #
    wph
    cc0
    cn0
    wcel
    #
    c1
    cn0
    wcel
    #
    @10
    0nn0
    1nn0
    cc0
    c1
    cn0
    prssi
    mp2an
    a1i
    brmptiunrelexpd
    @11
    @12
    @4
    @9
    wb
    0nn0
    1nn0
    @2
    @6
    @8
    vn
    cc0
    c1
    cn0
    cn0
    @0
    cc0
    wceq
    @1
    @5
    cA
    cB
    @0
    cc0
    cR
    crelexp
    oveq2
    breqd
    @0
    c1
    wceq
    @1
    @7
    cA
    cB
    @0
    c1
    cR
    crelexp
    oveq2
    breqd
    rexprg
    mp2an
    syl6bb
end
