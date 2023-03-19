include "csrg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "eqid.mm"
include "srgmgp.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mndidcl.mm"
include "syl.mm"

theorem srgidcl
  let cB: class B
  let cR: class R
  let c.1: class .1.
  assume srgidcl.b: |- B = ( Base ` R )
  assume srgidcl.u: |- .1. = ( 1r ` R )


  assert |- ( R e. SRing -> .1. e. B )

  proof
    cR
    csrg
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
    srgmgp
    cB
    @0
    c.1
    cB
    cR
    @0
    @1
    srgidcl.b
    mgpbas
    cR
    c.1
    @0
    @1
    srgidcl.u
    ringidval
    mndidcl
    syl
end
