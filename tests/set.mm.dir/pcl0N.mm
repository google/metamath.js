include "chlt.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "cpolN.mm"
include "catm.mm"
include "0ss.mm"
include "eqid.mm"
include "pclss2polN.mm"
include "mpan2.mm"
include "2pol0N.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "syl.mm"

theorem pcl0N
  let cU: class U
  let cK: class K
  assume pcl0.c: |- U = ( PCl ` K )


  assert |- ( K e. HL -> ( U ` (/) ) = (/) )

  proof
    cK
    chlt
    wcel
    #
    c0
    cU
    cfv
    #
    c0
    wss
    @1
    c0
    wceq
    @0
    @1
    c0
    cK
    cpolN
    cfv
    #
    cfv
    @2
    cfv
    #
    c0
    @0
    c0
    cK
    catm
    cfv
    #
    wss
    @1
    @3
    wss
    @4
    0ss
    @4
    cU
    cK
    @2
    c0
    @4
    eqid
    @2
    eqid
    #
    pcl0.c
    pclss2polN
    mpan2
    cK
    @2
    @5
    2pol0N
    sseqtrd
    @1
    ss0
    syl
end
