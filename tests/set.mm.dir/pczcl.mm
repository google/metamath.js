include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "pczpre.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "pcprecl.mm"
include "sylan.mm"
include "simpld.mm"
include "eqeltrd.mm"

theorem pczcl
  let cP: class P
  let cN: class N
  let vx: setvar x


  assert |- ( ( P e. Prime /\ ( N e. ZZ /\ N =/= 0 ) ) -> ( P pCnt N ) e. NN0 )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    cN
    cc0
    wne
    wa
    #
    wa
    #
    cP
    cN
    cpc
    co
    cP
    vx
    cv
    cexp
    co
    cN
    cdvds
    wbr
    vx
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cn0
    cP
    @4
    vx
    cN
    @4
    eqid
    #
    pczpre
    @2
    @4
    cn0
    wcel
    #
    cP
    @4
    cexp
    co
    cN
    cdvds
    wbr
    #
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @1
    @6
    @7
    wa
    cP
    prmuz2
    @3
    cP
    @4
    vx
    cN
    @3
    eqid
    @5
    pcprecl
    sylan
    simpld
    eqeltrd
end
