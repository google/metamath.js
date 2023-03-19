include "csr.mm"
include "wcel.mm"
include "cstf.mm"
include "cfv.mm"
include "crg.mm"
include "cgrp.mm"
include "cbs.mm"
include "wceq.mm"
include "srngring.mm"
include "ringgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "stafval.mm"
include "4syl.mm"
include "coppr.mm"
include "crh.mm"
include "co.mm"
include "cghm.mm"
include "srngrhm.mm"
include "rhmghm.mm"
include "oppr0.mm"
include "ghmid.mm"
include "3syl.mm"
include "eqtr3d.mm"

theorem srng0
  let cR: class R
  let c.as: class .*
  let c.0: class .0.
  assume srng0.i: |- .* = ( *r ` R )
  assume srng0.z: |- .0. = ( 0g ` R )


  assert |- ( R e. *Ring -> ( .* ` .0. ) = .0. )

  proof
    cR
    csr
    wcel
    #
    c.0
    cR
    cstf
    cfv
    #
    cfv
    #
    c.0
    c.as
    cfv
    #
    c.0
    @0
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    c.0
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
    cR
    ringgrp
    @4
    cR
    c.0
    @4
    eqid
    #
    srng0.z
    grpidcl
    c.0
    @4
    cR
    @1
    c.as
    @5
    srng0.i
    @1
    eqid
    #
    stafval
    4syl
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
    @1
    cR
    @7
    cghm
    co
    wcel
    @2
    c.0
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
    @1
    rhmghm
    cR
    @7
    @1
    c.0
    c.0
    srng0.z
    cR
    @7
    c.0
    @8
    srng0.z
    oppr0
    ghmid
    3syl
    eqtr3d
end
