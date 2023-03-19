include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "catm.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "psubssat.mm"
include "3adant2.mm"
include "sstrd.mm"
include "pclvalN.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "elintrabg.mm"
include "ibi.mm"
include "syl6bi.mm"
include "sseq2.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "com13.mm"
include "imp.mm"
include "3adant1.mm"
include "syld.mm"

theorem elpcliN
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume elpcli.s: |- S = ( PSubSp ` K )
  assume elpcli.c: |- U = ( PCl ` K )


  assert |- ( ( ( K e. V /\ X C_ Y /\ Y e. S ) /\ Q e. ( U ` X ) ) -> Q e. Y )

  proof
    cK
    cV
    wcel
    #
    cX
    cY
    wss
    #
    cY
    cS
    wcel
    #
    w3a
    #
    cQ
    cX
    cU
    cfv
    #
    wcel
    #
    cQ
    cY
    wcel
    #
    @3
    @5
    cX
    vz
    cv
    #
    wss
    #
    cQ
    @7
    wcel
    #
    wi
    #
    vz
    cS
    wral
    #
    @6
    @3
    @5
    cQ
    @8
    vz
    cS
    crab
    cint
    #
    wcel
    #
    @11
    @3
    @4
    @12
    cQ
    @3
    @0
    cX
    cK
    catm
    cfv
    #
    wss
    @4
    @12
    wceq
    @0
    @1
    @2
    simp1
    @3
    cX
    cY
    @14
    @0
    @1
    @2
    simp2
    @0
    @2
    cY
    @14
    wss
    @1
    @14
    cV
    cS
    cK
    cY
    @14
    eqid
    #
    elpcli.s
    psubssat
    3adant2
    sstrd
    vz
    @14
    cS
    cU
    cK
    cV
    cX
    @15
    elpcli.s
    elpcli.c
    pclvalN
    syl2anc
    eleq2d
    @13
    @11
    @8
    vz
    cQ
    cS
    @12
    elintrabg
    ibi
    syl6bi
    @1
    @2
    @11
    @6
    wi
    #
    @0
    @1
    @2
    @16
    @11
    @2
    @1
    @6
    @10
    @1
    @6
    wi
    vz
    cY
    cS
    @7
    cY
    wceq
    @8
    @1
    @9
    @6
    @7
    cY
    cX
    sseq2
    @7
    cY
    cQ
    eleq2
    imbi12d
    rspccv
    com13
    imp
    3adant1
    syld
    imp
end
