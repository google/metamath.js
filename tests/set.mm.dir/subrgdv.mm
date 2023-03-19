include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cinvr.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "subrginv.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "ressmulr.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "cbs.mm"
include "cui.mm"
include "wss.mm"
include "subrgss.mm"
include "simp2.mm"
include "sseldd.mm"
include "subrguss.mm"
include "simp3.mm"
include "dvrval.mm"
include "syl2anc.mm"
include "subrgbas.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"

theorem subrgdv
  let cA: class A
  let c.dv: class ./
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cX: class X
  let cY: class Y
  assume subrgdv.1: |- S = ( R |`s A )
  assume subrgdv.2: |- ./ = ( /r ` R )
  assume subrgdv.3: |- U = ( Unit ` S )
  assume subrgdv.4: |- E = ( /r ` S )


  assert |- ( ( A e. ( SubRing ` R ) /\ X e. A /\ Y e. U ) -> ( X ./ Y ) = ( X E Y ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cX
    cA
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    #
    cX
    cY
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    cY
    cS
    cinvr
    cfv
    #
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    cX
    cY
    c.dv
    co
    #
    cX
    cY
    cE
    co
    #
    @4
    @8
    cX
    @10
    @7
    co
    @12
    @4
    @6
    @10
    cX
    @7
    @1
    @3
    @6
    @10
    wceq
    @2
    cA
    cR
    cS
    cU
    @5
    @9
    cY
    subrgdv.1
    @5
    eqid
    #
    subrgdv.3
    @9
    eqid
    #
    subrginv
    3adant2
    oveq2d
    @4
    @7
    @11
    cX
    @10
    @1
    @2
    @7
    @11
    wceq
    @3
    cA
    cR
    cS
    @7
    @0
    subrgdv.1
    @7
    eqid
    #
    ressmulr
    3ad2ant1
    oveqd
    eqtrd
    @4
    cX
    cR
    cbs
    cfv
    #
    wcel
    cY
    cR
    cui
    cfv
    #
    wcel
    @13
    @8
    wceq
    @4
    cA
    @18
    cX
    @1
    @2
    cA
    @18
    wss
    @3
    cA
    @18
    cR
    @18
    eqid
    #
    subrgss
    3ad2ant1
    @1
    @2
    @3
    simp2
    #
    sseldd
    @4
    cU
    @19
    cY
    @1
    @2
    cU
    @19
    wss
    @3
    cA
    cR
    cS
    @19
    cU
    subrgdv.1
    @19
    eqid
    #
    subrgdv.3
    subrguss
    3ad2ant1
    @1
    @2
    @3
    simp3
    #
    sseldd
    @18
    c.dv
    cR
    @7
    @19
    @5
    cX
    cY
    @20
    @17
    @22
    @15
    subrgdv.2
    dvrval
    syl2anc
    @4
    cX
    cS
    cbs
    cfv
    #
    wcel
    @3
    @14
    @12
    wceq
    @4
    cX
    cA
    @24
    @21
    @1
    @2
    cA
    @24
    wceq
    @3
    cA
    cR
    cS
    subrgdv.1
    subrgbas
    3ad2ant1
    eleqtrd
    @23
    @24
    cE
    cS
    @11
    cU
    @9
    cX
    cY
    @24
    eqid
    @11
    eqid
    subrgdv.3
    @16
    subrgdv.4
    dvrval
    syl2anc
    3eqtr4d
end
