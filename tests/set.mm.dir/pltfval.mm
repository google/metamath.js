include "wcel.mm"
include "cplt.mm"
include "cfv.mm"
include "cid.mm"
include "cdif.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "difeq1d.mm"
include "df-plt.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem pltfval
  let cA: class A
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let vp: setvar p
  assume pltval.l: |- .<_ = ( le ` K )
  assume pltval.s: |- .< = ( lt ` K )


  assert |- ( K e. A -> .< = ( .<_ \ _I ) )

  proof
    cK
    cA
    wcel
    #
    c.lt
    cK
    cplt
    cfv
    #
    c.le
    cid
    cdif
    #
    pltval.s
    @0
    cK
    cvv
    wcel
    @1
    @2
    wceq
    cK
    cA
    elex
    vp
    cK
    vp
    cv
    #
    cple
    cfv
    #
    cid
    cdif
    @2
    cvv
    cplt
    @3
    cK
    wceq
    #
    @4
    c.le
    cid
    @5
    @4
    cK
    cple
    cfv
    #
    c.le
    @3
    cK
    cple
    fveq2
    pltval.l
    syl6eqr
    difeq1d
    vp
    df-plt
    c.le
    cvv
    wcel
    @2
    cvv
    wcel
    c.le
    @6
    cvv
    pltval.l
    cK
    cple
    fvex
    eqeltri
    c.le
    cid
    cvv
    difexg
    ax-mp
    fvmpt
    syl
    syl5eq
end
