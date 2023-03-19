include "cfn.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "wn.mm"
include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "cv.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cnx.mm"
include "cmulr.mm"
include "cotp.mm"
include "cmmul.mm"
include "cop.mm"
include "csts.mm"
include "df-mat.mm"
include "mpt2ndm0.mm"
include "fveq2d.mm"
include "base0.mm"
include "syl6eqr.mm"

theorem matbas0
  let cR: class R
  let cN: class N
  let vn: setvar n
  let vr: setvar r


  assert |- ( -. ( N e. Fin /\ R e. _V ) -> ( Base ` ( N Mat R ) ) = (/) )

  proof
    cN
    cfn
    wcel
    cR
    cvv
    wcel
    wa
    wn
    #
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    c0
    cbs
    cfv
    c0
    @0
    @1
    c0
    cbs
    vn
    vr
    vr
    cv
    #
    vn
    cv
    #
    @3
    cxp
    cfrlm
    co
    cnx
    cmulr
    cfv
    @2
    @3
    @3
    @3
    cotp
    cmmul
    co
    cop
    csts
    co
    cmat
    cN
    cR
    cfn
    cvv
    vn
    vr
    df-mat
    mpt2ndm0
    fveq2d
    base0
    syl6eqr
end
