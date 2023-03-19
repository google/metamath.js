include "clmod.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "csn.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "lsssn0.mm"
include "0ss.mm"
include "lspssp.mm"
include "mp3an3.mm"
include "mpdan.mm"
include "cbs.mm"
include "lspcl.mm"
include "mpan2.mm"
include "lss0ss.mm"
include "eqssd.mm"

theorem lsp0
  let cN: class N
  let cW: class W
  let c.0: class .0.
  assume lspsn0.z: |- .0. = ( 0g ` W )
  assume lspsn0.n: |- N = ( LSpan ` W )


  assert |- ( W e. LMod -> ( N ` (/) ) = { .0. } )

  proof
    cW
    clmod
    wcel
    #
    c0
    cN
    cfv
    #
    c.0
    csn
    #
    @0
    @2
    cW
    clss
    cfv
    #
    wcel
    #
    @1
    @2
    wss
    #
    @3
    cW
    c.0
    lspsn0.z
    @3
    eqid
    #
    lsssn0
    @0
    @4
    c0
    @2
    wss
    @5
    @2
    0ss
    @3
    c0
    @2
    cN
    cW
    @6
    lspsn0.n
    lspssp
    mp3an3
    mpdan
    @0
    @1
    @3
    wcel
    #
    @2
    @1
    wss
    @0
    c0
    cW
    cbs
    cfv
    #
    wss
    @7
    @8
    0ss
    @3
    c0
    cN
    @8
    cW
    @8
    eqid
    @6
    lspsn0.n
    lspcl
    mpan2
    @3
    cW
    @1
    c.0
    lspsn0.z
    @6
    lss0ss
    mpdan
    eqssd
end
