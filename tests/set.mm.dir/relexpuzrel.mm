include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "c1.mm"
include "wceq.mm"
include "wrel.mm"
include "wi.mm"
include "crelexp.mm"
include "co.mm"
include "eluzge2nn0.mm"
include "adantr.mm"
include "simpr.mm"
include "wne.mm"
include "cn.mm"
include "eluz2b3.mm"
include "simprbi.mm"
include "neneqd.mm"
include "pm2.21d.mm"
include "relexprelg.mm"
include "syl3anc.mm"

theorem relexpuzrel
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ R e. V ) -> Rel ( R ^r N ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    @1
    cN
    c1
    wceq
    #
    cR
    wrel
    #
    wi
    cR
    cN
    crelexp
    co
    wrel
    @0
    @3
    @1
    cN
    eluzge2nn0
    adantr
    @0
    @1
    simpr
    @2
    @4
    @5
    @2
    cN
    c1
    @0
    cN
    c1
    wne
    #
    @1
    @0
    cN
    cn
    wcel
    @6
    cN
    eluz2b3
    simprbi
    adantr
    neneqd
    pm2.21d
    cR
    cN
    cV
    relexprelg
    syl3anc
end
