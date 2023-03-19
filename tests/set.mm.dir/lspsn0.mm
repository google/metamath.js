include "clmod.mm"
include "wcel.mm"
include "csn.mm"
include "clss.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "lsssn0.mm"
include "lspid.mm"
include "mpdan.mm"

theorem lspsn0
  let cN: class N
  let cW: class W
  let c.0: class .0.
  assume lspsn0.z: |- .0. = ( 0g ` W )
  assume lspsn0.n: |- N = ( LSpan ` W )


  assert |- ( W e. LMod -> ( N ` { .0. } ) = { .0. } )

  proof
    cW
    clmod
    wcel
    c.0
    csn
    #
    cW
    clss
    cfv
    #
    wcel
    @0
    cN
    cfv
    @0
    wceq
    @1
    cW
    c.0
    lspsn0.z
    @1
    eqid
    #
    lsssn0
    @1
    @0
    cN
    cW
    @2
    lspsn0.n
    lspid
    mpdan
end
