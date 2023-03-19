include "clmod.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "cuni.mm"
include "csn.mm"
include "lsp0.mm"
include "unieqd.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "unisn.mm"
include "syl6eq.mm"

theorem lspuni0
  let cN: class N
  let cW: class W
  let c.0: class .0.
  assume lspsn0.z: |- .0. = ( 0g ` W )
  assume lspsn0.n: |- N = ( LSpan ` W )


  assert |- ( W e. LMod -> U. ( N ` (/) ) = .0. )

  proof
    cW
    clmod
    wcel
    #
    c0
    cN
    cfv
    #
    cuni
    c.0
    csn
    #
    cuni
    c.0
    @0
    @1
    @2
    cN
    cW
    c.0
    lspsn0.z
    lspsn0.n
    lsp0
    unieqd
    c.0
    c.0
    cW
    c0g
    cfv
    cvv
    lspsn0.z
    cW
    c0g
    fvex
    eqeltri
    unisn
    syl6eq
end
