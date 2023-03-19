include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "cword.mm"
include "w3a.mm"
include "cwwlksn.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "wwlknbp.mm"
include "wi.mm"
include "cwwlks.mm"
include "wa.mm"
include "iswwlksn.mm"
include "c0.mm"
include "wne.mm"
include "cmin.mm"
include "iswwlks.mm"
include "simpl2.mm"
include "simprl.mm"
include "oveq1.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "syl.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "biimpcd.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "3jca.mm"
include "ex.mm"
include "sylbi.mm"
include "expdimp.mm"
include "com12.mm"
include "sylbid.mm"
include "3ad2ant2.mm"
include "mpcom.mm"

theorem wwlknp
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  assume wwlkbp.v: |- V = ( Vtx ` G )
  assume wwlknp.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  disjoint N i
  disjoint g n
  disjoint g w
  disjoint n w
  assert |- ( W e. ( N WWalksN G ) -> ( W e. Word V /\ ( # ` W ) = ( N + 1 ) /\ A. i e. ( 0 ..^ N ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E ) )

  proof
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    w3a
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @2
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    @7
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    #
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    w3a
    #
    cG
    cN
    cV
    cW
    wwlkbp.v
    wwlknbp
    @1
    @0
    @3
    @11
    wi
    @2
    @1
    @3
    cW
    cG
    cwwlks
    cfv
    wcel
    #
    @6
    wa
    #
    @11
    cG
    cN
    cW
    iswwlksn
    @13
    @1
    @11
    @12
    @6
    @1
    @11
    @12
    cW
    c0
    wne
    #
    @2
    @8
    vi
    cc0
    @4
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @6
    @1
    wa
    #
    @11
    wi
    vi
    cE
    cG
    cV
    cW
    wwlkbp.v
    wwlknp.e
    iswwlks
    @18
    @19
    @11
    @18
    @19
    wa
    @2
    @6
    @10
    @14
    @2
    @17
    @19
    simpl2
    @18
    @6
    @1
    simprl
    @18
    @19
    @10
    @17
    @14
    @19
    @10
    wi
    @2
    @19
    @17
    @10
    @19
    @8
    vi
    @16
    @9
    @19
    @15
    cN
    cc0
    cfzo
    @6
    @1
    @15
    @5
    c1
    cmin
    co
    #
    cN
    @4
    @5
    c1
    cmin
    oveq1
    @1
    cN
    cc
    wcel
    @20
    cN
    wceq
    cN
    nn0cn
    cN
    pncan1
    syl
    sylan9eq
    oveq2d
    raleqdv
    biimpcd
    3ad2ant3
    imp
    3jca
    ex
    sylbi
    expdimp
    com12
    sylbid
    3ad2ant2
    mpcom
end
