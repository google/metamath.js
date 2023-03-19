include "cc0.mm"
include "ccxp.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "c1.mm"
include "oveq2.mm"
include "cc.mm"
include "wcel.mm"
include "0cn.mm"
include "cxp0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "wne.mm"
include "wa.mm"
include "cxpcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mul01d.mm"
include "0cxp.mm"
include "sylan.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "syl.mm"
include "oveq1d.mm"
include "1t1e1.mm"
include "syl6req.mm"
include "pm2.61ne.mm"

theorem mulcxplem
  let wph: wff ph
  let cA: class A
  let cC: class C
  assume mulcxp.1: |- ( ph -> A e. CC )
  assume mulcxp.2: |- ( ph -> C e. CC )


  assert |- ( ph -> ( 0 ^c C ) = ( ( A ^c C ) x. ( 0 ^c C ) ) )

  proof
    wph
    cc0
    cC
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    @0
    cmul
    co
    #
    wceq
    c1
    cA
    cc0
    ccxp
    co
    #
    c1
    cmul
    co
    #
    wceq
    cC
    cc0
    cC
    cc0
    wceq
    #
    @0
    c1
    @2
    @4
    @5
    @0
    cc0
    cc0
    ccxp
    co
    #
    c1
    cC
    cc0
    cc0
    ccxp
    oveq2
    cc0
    cc
    wcel
    @6
    c1
    wceq
    0cn
    cc0
    cxp0
    ax-mp
    syl6eq
    #
    @5
    @1
    @3
    @0
    c1
    cmul
    cC
    cc0
    cA
    ccxp
    oveq2
    @7
    oveq12d
    eqeq12d
    wph
    cC
    cc0
    wne
    #
    wa
    #
    @1
    cc0
    cmul
    co
    cc0
    @2
    @0
    @9
    @1
    wph
    @1
    cc
    wcel
    #
    @8
    wph
    cA
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    @10
    mulcxp.1
    mulcxp.2
    cA
    cC
    cxpcl
    syl2anc
    adantr
    mul01d
    @9
    @0
    cc0
    @1
    cmul
    wph
    @12
    @8
    @0
    cc0
    wceq
    mulcxp.2
    cC
    0cxp
    sylan
    #
    oveq2d
    @13
    3eqtr4rd
    wph
    @4
    c1
    c1
    cmul
    co
    c1
    wph
    @3
    c1
    c1
    cmul
    wph
    @11
    @3
    c1
    wceq
    mulcxp.1
    cA
    cxp0
    syl
    oveq1d
    1t1e1
    syl6req
    pm2.61ne
end
