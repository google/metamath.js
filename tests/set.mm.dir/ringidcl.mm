include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mndidcl.mm"
include "syl.mm"

theorem ringidcl
  let cB: class B
  let cR: class R
  let c.1: class .1.
  assume ringidcl.b: |- B = ( Base ` R )
  assume ringidcl.u: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> .1. e. B )

  proof
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    c.1
    cB
    wcel
    cR
    @0
    @0
    eqid
    #
    ringmgp
    cB
    @0
    c.1
    cB
    cR
    @0
    @1
    ringidcl.b
    mgpbas
    cR
    c.1
    @0
    @1
    ringidcl.u
    ringidval
    mndidcl
    syl
end
