include "wcel.mm"
include "wa.mm"
include "cpws.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "id.mm"
include "sneq.mm"
include "xpeq12.mm"
include "syl2anr.mm"
include "oveq12d.mm"
include "df-pws.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem pwsval
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vi: setvar i
  let vr: setvar r
  assume pwsval.y: |- Y = ( R ^s I )
  assume pwsval.f: |- F = ( Scalar ` R )


  assert |- ( ( R e. V /\ I e. W ) -> Y = ( F Xs_ ( I X. { R } ) ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    cY
    cR
    cI
    cpws
    co
    #
    cF
    cI
    cR
    csn
    #
    cxp
    #
    cprds
    co
    #
    pwsval.y
    @0
    cR
    cvv
    wcel
    cI
    cvv
    wcel
    @2
    @5
    wceq
    @1
    cR
    cV
    elex
    cI
    cW
    elex
    vr
    vi
    cR
    cI
    cvv
    cvv
    vr
    cv
    #
    csca
    cfv
    #
    vi
    cv
    #
    @6
    csn
    #
    cxp
    #
    cprds
    co
    @5
    cpws
    @6
    cR
    wceq
    #
    @8
    cI
    wceq
    #
    wa
    #
    @7
    cF
    @10
    @4
    cprds
    @13
    @7
    cR
    csca
    cfv
    cF
    @13
    @6
    cR
    csca
    @11
    @12
    simpl
    fveq2d
    pwsval.f
    syl6eqr
    @12
    @12
    @9
    @3
    wceq
    @10
    @4
    wceq
    @11
    @12
    id
    @6
    cR
    sneq
    @8
    cI
    @9
    @3
    xpeq12
    syl2anr
    oveq12d
    vi
    vr
    df-pws
    cF
    @4
    cprds
    ovex
    ovmpt2a
    syl2an
    syl5eq
end
