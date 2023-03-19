include "cv.mm"
include "wdisj.mm"
include "c0.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "ssequn2.mm"
include "sylib.mm"
include "disjeq1d.mm"
include "biimparc.mm"
include "wn.mm"
include "wa.mm"
include "ciun.mm"
include "cin.mm"
include "simpl.mm"
include "in0.mm"
include "a1i.mm"
include "wb.mm"
include "cvv.mm"
include "0ex.mm"
include "id.mm"
include "disjunsn.mm"
include "mpan.mm"
include "adantl.mm"
include "mpbir2and.mm"
include "pm2.61dan.mm"

theorem disjun0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Disj_ x e. A x -> Disj_ x e. ( A u. { (/) } ) x )

  proof
    vx
    cA
    vx
    cv
    #
    wdisj
    #
    c0
    cA
    wcel
    #
    vx
    cA
    c0
    csn
    #
    cun
    #
    @0
    wdisj
    #
    @2
    @5
    @1
    @2
    vx
    @4
    cA
    @0
    @2
    @3
    cA
    wss
    @4
    cA
    wceq
    c0
    cA
    snssi
    @3
    cA
    ssequn2
    sylib
    disjeq1d
    biimparc
    @1
    @2
    wn
    #
    wa
    #
    @5
    @1
    vx
    cA
    @0
    ciun
    #
    c0
    cin
    c0
    wceq
    #
    @1
    @6
    simpl
    @9
    @7
    @8
    in0
    a1i
    @6
    @5
    @1
    @9
    wa
    wb
    #
    @1
    c0
    cvv
    wcel
    @6
    @10
    0ex
    vx
    cA
    @0
    c0
    c0
    cvv
    @0
    c0
    wceq
    id
    disjunsn
    mpan
    adantl
    mpbir2and
    pm2.61dan
end
