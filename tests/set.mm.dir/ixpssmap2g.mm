include "ciun.mm"
include "wcel.mm"
include "cixp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "wf.mm"
include "ixpf.mm"
include "adantl.mm"
include "cvv.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "ixpprc.mm"
include "nsyl2.mm"
include "elmapg.mm"
include "sylan2.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ixpssmap2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f

  disjoint A x
  disjoint A f
  disjoint f x
  disjoint B f
  disjoint V f
  assert |- ( U_ x e. A B e. V -> X_ x e. A B C_ ( U_ x e. A B ^m A ) )

  proof
    vx
    cA
    cB
    ciun
    #
    cV
    wcel
    #
    vf
    vx
    cA
    cB
    cixp
    #
    @0
    cA
    cmap
    co
    #
    @1
    vf
    cv
    #
    @2
    wcel
    #
    @4
    @3
    wcel
    #
    @1
    @5
    wa
    @6
    cA
    @0
    @4
    wf
    #
    @5
    @7
    @1
    vx
    cA
    cB
    @4
    ixpf
    adantl
    @5
    @1
    cA
    cvv
    wcel
    #
    @6
    @7
    wb
    @5
    @2
    c0
    wceq
    @8
    @2
    @4
    n0i
    vx
    cA
    cB
    ixpprc
    nsyl2
    @0
    cA
    @4
    cV
    cvv
    elmapg
    sylan2
    mpbird
    ex
    ssrdv
end
