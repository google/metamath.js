include "clno.mm"
include "co.mm"
include "wcel.mm"
include "ccn.mm"
include "cnv.mm"
include "eqid.mm"
include "bloln.mm"
include "mp3an12.mm"
include "blocn.mm"
include "biimprd.mm"
include "mpcom.mm"

theorem blocn2
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cW: class W
  assume blocn.8: |- C = ( IndMet ` U )
  assume blocn.d: |- D = ( IndMet ` W )
  assume blocn.j: |- J = ( MetOpen ` C )
  assume blocn.k: |- K = ( MetOpen ` D )
  assume blocn.5: |- B = ( U BLnOp W )
  assume blocn.u: |- U e. NrmCVec
  assume blocn.w: |- W e. NrmCVec


  assert |- ( T e. B -> T e. ( J Cn K ) )

  proof
    cT
    cU
    cW
    clno
    co
    #
    wcel
    #
    cT
    cB
    wcel
    #
    cT
    cJ
    cK
    ccn
    co
    wcel
    #
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    @2
    @1
    blocn.u
    blocn.w
    cB
    cT
    cU
    @0
    cW
    @0
    eqid
    #
    blocn.5
    bloln
    mp3an12
    @1
    @3
    @2
    cB
    cC
    cD
    cT
    cU
    cJ
    cK
    @0
    cW
    blocn.8
    blocn.d
    blocn.j
    blocn.k
    blocn.5
    blocn.u
    blocn.w
    @4
    blocn
    biimprd
    mpcom
end
