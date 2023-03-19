include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cv.mm"
include "crab.mm"
include "wf.mm"
include "coe1f.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nn0ex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "coe1sfi.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"

theorem coe1fsupp
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let vg: setvar g
  let cF: class F
  let cK: class K
  let c.0: class .0.
  let vy: setvar y
  let vx: setvar x
  assume coe1sfi.a: |- A = ( coe1 ` F )
  assume coe1sfi.b: |- B = ( Base ` P )
  assume coe1sfi.p: |- P = ( Poly1 ` R )
  assume coe1sfi.z: |- .0. = ( 0g ` R )
  assume coe1fvalcl.k: |- K = ( Base ` R )

  disjoint A g
  disjoint K g
  disjoint .0. g
  disjoint B y
  disjoint F y
  disjoint x y
  assert |- ( F e. B -> A e. { g e. ( K ^m NN0 ) | g finSupp .0. } )

  proof
    cF
    cB
    wcel
    #
    cA
    cK
    cn0
    cmap
    co
    #
    wcel
    #
    cA
    c.0
    cfsupp
    wbr
    #
    cA
    vg
    cv
    #
    c.0
    cfsupp
    wbr
    #
    vg
    @1
    crab
    wcel
    @0
    @2
    cn0
    cK
    cA
    wf
    #
    cA
    cB
    cP
    cR
    cF
    cK
    coe1sfi.a
    coe1sfi.b
    coe1sfi.p
    coe1fvalcl.k
    coe1f
    cK
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    wa
    @2
    @6
    wb
    @0
    @7
    @8
    cK
    cR
    cbs
    cfv
    cvv
    coe1fvalcl.k
    cR
    cbs
    fvex
    eqeltri
    nn0ex
    pm3.2i
    cK
    cn0
    cA
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    cA
    cB
    cP
    cR
    cF
    c.0
    coe1sfi.a
    coe1sfi.b
    coe1sfi.p
    coe1sfi.z
    coe1sfi
    @5
    @3
    vg
    cA
    @1
    @4
    cA
    c.0
    cfsupp
    breq1
    elrab
    sylanbrc
end
