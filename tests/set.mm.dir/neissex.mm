include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "neii2.mm"
include "opnneiss.mm"
include "3expb.mm"
include "adantrrr.mm"
include "adantlr.mm"
include "simplll.mm"
include "cuni.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "eqid.mm"
include "neii1.mm"
include "adantr.mm"
include "opnssneib.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "anasss.mm"
include "neiss.mm"
include "ex.mm"
include "adantrrl.mm"
include "alrimiv.mm"
include "jca.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem neissex
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cJ: class J
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let cM: class M

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint J h
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint M g
  disjoint M h
  disjoint M v
  disjoint N g
  disjoint N h
  disjoint N v
  disjoint S g
  disjoint S h
  disjoint S v
  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) ) -> E. x e. ( ( nei ` J ) ` S ) A. y ( y C_ x -> N e. ( ( nei ` J ) ` y ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    #
    cfv
    #
    wcel
    #
    wa
    #
    cS
    vx
    cv
    #
    wss
    #
    @5
    cN
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    vy
    cv
    #
    @5
    wss
    #
    cN
    @9
    @1
    cfv
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    @2
    wrex
    cS
    vx
    cJ
    cN
    neii2
    @4
    @8
    @13
    vx
    cJ
    @2
    @4
    @5
    cJ
    wcel
    #
    @8
    wa
    #
    @5
    @2
    wcel
    #
    @13
    wa
    @4
    @15
    wa
    #
    @16
    @13
    @0
    @15
    @16
    @3
    @0
    @14
    @6
    @16
    @7
    @0
    @14
    @6
    @16
    cS
    cJ
    @5
    opnneiss
    3expb
    adantrrr
    adantlr
    @17
    @12
    vy
    @4
    @14
    @7
    @12
    @6
    @4
    @14
    @7
    wa
    #
    wa
    #
    @10
    @11
    @19
    @10
    wa
    @0
    cN
    @5
    @1
    cfv
    wcel
    #
    @10
    @11
    @0
    @3
    @18
    @10
    simplll
    @19
    @20
    @10
    @4
    @14
    @7
    @20
    @4
    @14
    wa
    #
    @7
    @20
    @21
    @0
    @14
    cN
    cJ
    cuni
    #
    wss
    #
    @7
    @20
    wb
    @0
    @3
    @14
    simpll
    @4
    @14
    simpr
    @4
    @23
    @14
    cS
    cJ
    cN
    @22
    @22
    eqid
    #
    neii1
    adantr
    @5
    cJ
    cN
    @22
    @24
    opnssneib
    syl3anc
    biimpa
    anasss
    adantr
    @19
    @10
    simpr
    @9
    @5
    cJ
    cN
    neiss
    syl3anc
    ex
    adantrrl
    alrimiv
    jca
    ex
    reximdv2
    mpd
end
