include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cprime.mm"
include "wcel.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "wa.mm"
include "sq0i.mm"
include "oveq1d.mm"
include "zcnd.mm"
include "sqcld.mm"
include "addid2d.mm"
include "sylan9eqr.mm"
include "wn.mm"
include "cz.mm"
include "sqnprm.mm"
include "syl.mm"
include "eqneltrd.mm"
include "pm2.65da.mm"
include "neqned.mm"

theorem 2sqn0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  assume 2sqcoprm.1: |- ( ph -> P e. Prime )
  assume 2sqcoprm.2: |- ( ph -> A e. ZZ )
  assume 2sqcoprm.3: |- ( ph -> B e. ZZ )
  assume 2sqcoprm.4: |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = P )


  assert |- ( ph -> A =/= 0 )

  proof
    wph
    cA
    cc0
    wph
    cA
    cc0
    wceq
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cprime
    wcel
    #
    wph
    @4
    @0
    wph
    @3
    cP
    cprime
    2sqcoprm.4
    2sqcoprm.1
    eqeltrd
    adantr
    wph
    @0
    wa
    @3
    @2
    cprime
    @0
    wph
    @3
    cc0
    @2
    caddc
    co
    @2
    @0
    @1
    cc0
    @2
    caddc
    cA
    sq0i
    oveq1d
    wph
    @2
    wph
    cB
    wph
    cB
    2sqcoprm.3
    zcnd
    sqcld
    addid2d
    sylan9eqr
    wph
    @2
    cprime
    wcel
    wn
    #
    @0
    wph
    cB
    cz
    wcel
    @5
    2sqcoprm.3
    cB
    sqnprm
    syl
    adantr
    eqneltrd
    pm2.65da
    neqned
end
