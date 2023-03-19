include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cv.mm"
include "crglmod.mm"
include "cfv.mm"
include "cxp.mm"
include "cbs.mm"
include "cixp.mm"
include "wfn.mm"
include "csb.mm"
include "cab.mm"
include "wceq.mm"
include "ixpsnval.mm"
include "adantl.mm"
include "csbfv2g.mm"
include "csbvarg.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "cop.mm"
include "cvv.mm"
include "fvexd.mm"
include "anim1i.mm"
include "ancomd.mm"
include "xpsng.mm"
include "syl.mm"
include "fveq1d.mm"
include "fvsng.mm"
include "rlmbas.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "abbidv.mm"

theorem ixpsnbasval
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X

  disjoint R f
  disjoint R x
  disjoint f x
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint X x
  assert |- ( ( R e. V /\ X e. W ) -> X_ x e. { X } ( Base ` ( ( { X } X. { ( ringLMod ` R ) } ) ` x ) ) = { f | ( f Fn { X } /\ ( f ` X ) e. ( Base ` R ) ) } )

  proof
    cR
    cV
    wcel
    #
    cX
    cW
    wcel
    #
    wa
    #
    vx
    cX
    csn
    #
    vx
    cv
    #
    @3
    cR
    crglmod
    cfv
    #
    csn
    cxp
    #
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    vf
    cv
    #
    @3
    wfn
    #
    cX
    @10
    cfv
    #
    vx
    cX
    @8
    csb
    #
    wcel
    #
    wa
    #
    vf
    cab
    #
    @11
    @12
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    vf
    cab
    @1
    @9
    @16
    wceq
    @0
    vx
    @8
    vf
    cW
    cX
    ixpsnval
    adantl
    @2
    @15
    @19
    vf
    @2
    @14
    @18
    @11
    @2
    @13
    @17
    @12
    @2
    @13
    @5
    cbs
    cfv
    #
    @17
    @2
    @13
    cX
    @6
    cfv
    #
    cbs
    cfv
    #
    @20
    @1
    @13
    @22
    wceq
    @0
    @1
    @13
    vx
    cX
    @7
    csb
    #
    cbs
    cfv
    @22
    vx
    cX
    @7
    cW
    cbs
    csbfv2g
    @1
    @23
    @21
    cbs
    @1
    @23
    vx
    cX
    @4
    csb
    #
    @6
    cfv
    @21
    vx
    cX
    @4
    cW
    @6
    csbfv2g
    @1
    @24
    cX
    @6
    vx
    cX
    cW
    csbvarg
    fveq2d
    eqtrd
    fveq2d
    eqtrd
    adantl
    @2
    @21
    @5
    cbs
    @2
    @21
    cX
    cX
    @5
    cop
    csn
    #
    cfv
    #
    @5
    @2
    cX
    @6
    @25
    @2
    @1
    @5
    cvv
    wcel
    #
    wa
    #
    @6
    @25
    wceq
    @2
    @27
    @1
    @0
    @27
    @1
    @0
    cR
    crglmod
    fvexd
    anim1i
    ancomd
    #
    cX
    @5
    cW
    cvv
    xpsng
    syl
    fveq1d
    @2
    @28
    @26
    @5
    wceq
    @29
    cX
    @5
    cW
    cvv
    fvsng
    syl
    eqtrd
    fveq2d
    eqtrd
    cR
    rlmbas
    syl6eqr
    eleq2d
    anbi2d
    abbidv
    eqtrd
end
