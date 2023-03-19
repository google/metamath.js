include "cn0.mm"
include "wcel.mm"
include "zring.mm"
include "csn.mm"
include "crsp.mm"
include "cfv.mm"
include "cqg.mm"
include "co.mm"
include "cqus.mm"
include "ccrg.mm"
include "cz.mm"
include "nn0z.mm"
include "eqid.mm"
include "zncrng2.mm"
include "syl.mm"
include "cbs.mm"
include "eqidd.mm"
include "znbas2.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "znadd.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "znmul.mm"
include "crngpropd.mm"
include "mpbid.mm"

theorem zncrng
  let cN: class N
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume zncrng.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. NN0 -> Y e. CRing )

  proof
    cN
    cn0
    wcel
    #
    zring
    zring
    cN
    csn
    zring
    crsp
    cfv
    #
    cfv
    cqg
    co
    cqus
    co
    #
    ccrg
    wcel
    #
    cY
    ccrg
    wcel
    @0
    cN
    cz
    wcel
    @3
    cN
    nn0z
    @1
    @2
    cN
    @1
    eqid
    #
    @2
    eqid
    #
    zncrng2
    syl
    @0
    vx
    vy
    @2
    cbs
    cfv
    #
    @2
    cY
    @0
    @6
    eqidd
    @1
    @2
    cN
    cY
    @4
    @5
    zncrng.y
    znbas2
    @0
    vx
    cv
    @6
    wcel
    vy
    cv
    @6
    wcel
    wa
    #
    vx
    vy
    @2
    cplusg
    cfv
    cY
    cplusg
    cfv
    @1
    @2
    cN
    cY
    @4
    @5
    zncrng.y
    znadd
    oveqdr
    @0
    @7
    vx
    vy
    @2
    cmulr
    cfv
    cY
    cmulr
    cfv
    @1
    @2
    cN
    cY
    @4
    @5
    zncrng.y
    znmul
    oveqdr
    crngpropd
    mpbid
end
