include "cid.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "c1.mm"
include "csn.mm"
include "wrex.mm"
include "dfid6.mm"
include "cn0.mm"
include "wcel.mm"
include "wss.mm"
include "1nn0.mm"
include "snssi.mm"
include "mp1i.mm"
include "brmptiunrelexpd.mm"
include "wb.mm"
include "wceq.mm"
include "oveq2.mm"
include "breqd.mm"
include "rexsng.mm"
include "relexp1d.mm"
include "3bitrd.mm"

theorem brfvidRP
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume brfvidRP.r: |- ( ph -> R e. _V )


  assert |- ( ph -> ( A ( _I ` R ) B <-> A R B ) )

  proof
    wph
    cA
    cB
    cR
    cid
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
    c1
    csn
    #
    wrex
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
    cA
    cB
    cR
    wbr
    wph
    cA
    cB
    cid
    cR
    vn
    @3
    vr
    vr
    vn
    dfid6
    brfvidRP.r
    c1
    cn0
    wcel
    #
    @3
    cn0
    wss
    wph
    1nn0
    c1
    cn0
    snssi
    mp1i
    brmptiunrelexpd
    @7
    @4
    @6
    wb
    wph
    1nn0
    @2
    @6
    vn
    c1
    cn0
    @0
    c1
    wceq
    @1
    @5
    cA
    cB
    @0
    c1
    cR
    crelexp
    oveq2
    breqd
    rexsng
    mp1i
    wph
    @5
    cR
    cA
    cB
    wph
    cR
    brfvidRP.r
    relexp1d
    breqd
    3bitrd
end
