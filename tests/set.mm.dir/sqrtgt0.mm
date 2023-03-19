include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cle.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "imp.mm"
include "resqrtcl.mm"
include "syldan.mm"
include "sqrtge0.mm"
include "wne.mm"
include "gt0ne0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "sq0i.mm"
include "resqrtth.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "necon3d.mm"
include "mpd.mm"
include "ne0gt0d.mm"

theorem sqrtgt0
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A ) -> 0 < ( sqrt ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cA
    csqrt
    cfv
    #
    @0
    @1
    cc0
    cA
    cle
    wbr
    #
    @3
    cr
    wcel
    @0
    @1
    @4
    cc0
    cr
    wcel
    @0
    @1
    @4
    wi
    0re
    cc0
    cA
    ltle
    mpan
    imp
    #
    cA
    resqrtcl
    syldan
    @0
    @1
    @4
    cc0
    @3
    cle
    wbr
    @5
    cA
    sqrtge0
    syldan
    @2
    cA
    cc0
    wne
    @3
    cc0
    wne
    cA
    gt0ne0
    @2
    @3
    cc0
    cA
    cc0
    @3
    cc0
    wceq
    @3
    c2
    cexp
    co
    #
    cc0
    wceq
    @2
    cA
    cc0
    wceq
    @3
    sq0i
    @2
    @6
    cA
    cc0
    @0
    @1
    @4
    @6
    cA
    wceq
    @5
    cA
    resqrtth
    syldan
    eqeq1d
    syl5ib
    necon3d
    mpd
    ne0gt0d
end
