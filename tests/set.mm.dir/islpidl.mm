include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "ciun.mm"
include "wceq.mm"
include "wrex.mm"
include "lpival.mm"
include "eleq2d.mm"
include "eliun.mm"
include "fvex.mm"
include "elsn2.mm"
include "rexbii.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem islpidl
  let cB: class B
  let cP: class P
  let cR: class R
  let vg: setvar g
  let cI: class I
  let cK: class K
  let vr: setvar r
  let cU: class U
  let c.0: class .0.
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpival.k: |- K = ( RSpan ` R )
  assume lpival.b: |- B = ( Base ` R )

  disjoint R g
  disjoint P g
  disjoint B g
  disjoint K g
  disjoint I g
  disjoint R r
  disjoint g r
  disjoint P r
  disjoint B r
  disjoint K r
  disjoint U g
  disjoint .0. g
  assert |- ( R e. Ring -> ( I e. P <-> E. g e. B I = ( K ` { g } ) ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cP
    wcel
    cI
    vg
    cB
    vg
    cv
    csn
    #
    cK
    cfv
    #
    csn
    #
    ciun
    #
    wcel
    #
    cI
    @2
    wceq
    #
    vg
    cB
    wrex
    #
    @0
    cP
    @4
    cI
    cB
    cP
    cR
    vg
    cK
    lpival.p
    lpival.k
    lpival.b
    lpival
    eleq2d
    @5
    cI
    @3
    wcel
    #
    vg
    cB
    wrex
    @7
    vg
    cI
    cB
    @3
    eliun
    @8
    @6
    vg
    cB
    cI
    @2
    @1
    cK
    fvex
    elsn2
    rexbii
    bitri
    syl6bb
end
