include "csr.mm"
include "wcel.mm"
include "cstf.mm"
include "cfv.mm"
include "crg.mm"
include "cbs.mm"
include "wceq.mm"
include "srngring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "stafval.mm"
include "3syl.mm"
include "coppr.mm"
include "crh.mm"
include "co.mm"
include "srngrhm.mm"
include "oppr1.mm"
include "rhm1.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem srng1
  let cR: class R
  let c.1: class .1.
  let c.as: class .*
  assume srng1.i: |- .* = ( *r ` R )
  assume srng1.t: |- .1. = ( 1r ` R )


  assert |- ( R e. *Ring -> ( .* ` .1. ) = .1. )

  proof
    cR
    csr
    wcel
    #
    c.1
    cR
    cstf
    cfv
    #
    cfv
    #
    c.1
    c.as
    cfv
    #
    c.1
    @0
    cR
    crg
    wcel
    c.1
    cR
    cbs
    cfv
    #
    wcel
    @2
    @3
    wceq
    cR
    srngring
    @4
    cR
    c.1
    @4
    eqid
    #
    srng1.t
    ringidcl
    c.1
    @4
    cR
    @1
    c.as
    @5
    srng1.i
    @1
    eqid
    #
    stafval
    3syl
    @0
    @1
    cR
    cR
    coppr
    cfv
    #
    crh
    co
    wcel
    @2
    c.1
    wceq
    cR
    @1
    @7
    @7
    eqid
    #
    @6
    srngrhm
    cR
    @7
    c.1
    @1
    c.1
    srng1.t
    cR
    c.1
    @7
    @8
    srng1.t
    oppr1
    rhm1
    syl
    eqtr3d
end
