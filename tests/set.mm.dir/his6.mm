include "chil.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "ax-his4.mm"
include "gt0ne0d.mm"
include "ex.mm"
include "necon4d.mm"
include "hi01.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem his6
  let cA: class A


  assert |- ( A e. ~H -> ( ( A .ih A ) = 0 <-> A = 0h ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cA
    csp
    co
    #
    cc0
    wceq
    #
    cA
    c0v
    wceq
    #
    @0
    cA
    c0v
    @1
    cc0
    @0
    cA
    c0v
    wne
    #
    @1
    cc0
    wne
    @0
    @4
    wa
    @1
    cA
    ax-his4
    gt0ne0d
    ex
    necon4d
    @0
    @2
    @3
    c0v
    cA
    csp
    co
    #
    cc0
    wceq
    cA
    hi01
    @3
    @1
    @5
    cc0
    cA
    c0v
    cA
    csp
    oveq1
    eqeq1d
    syl5ibrcom
    impbid
end
