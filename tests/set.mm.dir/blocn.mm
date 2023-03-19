include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "wb.mm"
include "c0o.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "bibi12d.mm"
include "cnv.mm"
include "eqid.mm"
include "0lno.mm"
include "mp2an.mm"
include "elimel.mm"
include "blocni.mm"
include "dedth.mm"

theorem blocn
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  assume blocn.8: |- C = ( IndMet ` U )
  assume blocn.d: |- D = ( IndMet ` W )
  assume blocn.j: |- J = ( MetOpen ` C )
  assume blocn.k: |- K = ( MetOpen ` D )
  assume blocn.5: |- B = ( U BLnOp W )
  assume blocn.u: |- U e. NrmCVec
  assume blocn.w: |- W e. NrmCVec
  assume blocn.4: |- L = ( U LnOp W )


  assert |- ( T e. L -> ( T e. ( J Cn K ) <-> T e. B ) )

  proof
    cT
    cL
    wcel
    #
    cT
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    cT
    cB
    wcel
    #
    wb
    @0
    cT
    cU
    cW
    c0o
    co
    #
    cif
    #
    @1
    wcel
    #
    @5
    cB
    wcel
    #
    wb
    cT
    @4
    cT
    @5
    wceq
    @2
    @6
    @3
    @7
    cT
    @5
    @1
    eleq1
    cT
    @5
    cB
    eleq1
    bibi12d
    cB
    cC
    cD
    @5
    cU
    cJ
    cK
    cL
    cW
    blocn.8
    blocn.d
    blocn.j
    blocn.k
    blocn.4
    blocn.5
    blocn.u
    blocn.w
    cT
    @4
    cL
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    @4
    cL
    wcel
    blocn.u
    blocn.w
    cU
    cL
    cW
    @4
    @4
    eqid
    blocn.4
    0lno
    mp2an
    elimel
    blocni
    dedth
end
