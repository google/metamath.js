include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cwwspthsn.mm"
include "co.mm"
include "cv.mm"
include "cwwspthsnon.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "wne.mm"
include "c0.mm"
include "wi.mm"
include "wspthsnonn0vne.mm"
include "ex.mm"
include "adantr.mm"
include "ne0i.mm"
include "impel.mm"
include "necomd.mm"
include "pm4.71rd.mm"
include "rexbidv.mm"
include "rexdifsn.mm"
include "syl6bbr.mm"
include "wspthsnwspthsnon.mm"
include "vex.mm"
include "wceq.mm"
include "eleq1w.mm"
include "elab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "dfiunv2.mm"
include "syl6eqr.mm"

theorem wspniunwspnon
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  let vw: setvar w
  assume wspniunwspnon.v: |- V = ( Vtx ` G )

  disjoint G x
  disjoint G y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint V y
  disjoint G p
  disjoint G w
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint w x
  disjoint w y
  disjoint N p
  disjoint N w
  disjoint U w
  disjoint V p
  disjoint V w
  assert |- ( ( N e. NN /\ G e. U ) -> ( N WSPathsN G ) = U_ x e. V U_ y e. ( V \ { x } ) ( x ( N WSPathsNOn G ) y ) )

  proof
    cN
    cn
    wcel
    #
    cG
    cU
    wcel
    #
    wa
    #
    cN
    cG
    cwwspthsn
    co
    #
    vp
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cN
    cG
    cwwspthsnon
    co
    co
    #
    wcel
    #
    vy
    cV
    @5
    csn
    cdif
    #
    wrex
    #
    vx
    cV
    wrex
    #
    vp
    cab
    #
    vx
    cV
    vy
    @9
    @7
    ciun
    ciun
    @2
    vw
    @3
    @12
    @2
    vw
    cv
    #
    @7
    wcel
    #
    vy
    cV
    wrex
    #
    vx
    cV
    wrex
    @14
    vy
    @9
    wrex
    #
    vx
    cV
    wrex
    #
    @13
    @3
    wcel
    @13
    @12
    wcel
    @2
    @15
    @16
    vx
    cV
    @2
    @15
    @6
    @5
    wne
    #
    @14
    wa
    #
    vy
    cV
    wrex
    @16
    @2
    @14
    @19
    vy
    cV
    @2
    @14
    @18
    @2
    @14
    @18
    @2
    @14
    wa
    @5
    @6
    @2
    @7
    c0
    wne
    #
    @5
    @6
    wne
    #
    @14
    @0
    @20
    @21
    wi
    @1
    @0
    @20
    @21
    cG
    cN
    @5
    @6
    wspthsnonn0vne
    ex
    adantr
    @7
    @13
    ne0i
    impel
    necomd
    ex
    pm4.71rd
    rexbidv
    @14
    vy
    cV
    @5
    rexdifsn
    syl6bbr
    rexbidv
    cG
    cN
    cV
    @13
    vx
    vy
    wspniunwspnon.v
    wspthsnwspthsnon
    @11
    @17
    vp
    @13
    vw
    vex
    @4
    @13
    wceq
    #
    @10
    @16
    vx
    cV
    @22
    @8
    @14
    vy
    @9
    vp
    vw
    @7
    eleq1w
    rexbidv
    rexbidv
    elab
    3bitr4g
    eqrdv
    vx
    vy
    vp
    cV
    @9
    @7
    dfiunv2
    syl6eqr
end
