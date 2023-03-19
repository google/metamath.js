include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantl.mm"
include "wb.mm"
include "elmapg.mm"
include "adantr.mm"
include "mpbird.mm"
include "fmptd.mm"

theorem fdiagfn
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  assume fdiagfn.f: |- F = ( x e. B |-> ( I X. { x } ) )

  disjoint B x
  disjoint I x
  disjoint V x
  disjoint W x
  disjoint X x
  assert |- ( ( B e. V /\ I e. W ) -> F : B --> ( B ^m I ) )

  proof
    cB
    cV
    wcel
    cI
    cW
    wcel
    wa
    #
    vx
    cB
    cI
    vx
    cv
    #
    csn
    cxp
    #
    cB
    cI
    cmap
    co
    #
    cF
    @0
    @1
    cB
    wcel
    #
    wa
    @2
    @3
    wcel
    #
    cI
    cB
    @2
    wf
    #
    @4
    @6
    @0
    cI
    @1
    cB
    fconst6g
    adantl
    @0
    @5
    @6
    wb
    @4
    cB
    cI
    @2
    cV
    cW
    elmapg
    adantr
    mpbird
    fdiagfn.f
    fmptd
end
