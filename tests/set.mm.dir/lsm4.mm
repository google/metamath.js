include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3l.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simp2l.mm"
include "lsmass.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "lsmsubg2.mm"
include "simp3r.mm"
include "3eqtr3d.mm"

theorem lsm4
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let cG: class G
  assume lsmcom.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( G e. Abel /\ ( Q e. ( SubGrp ` G ) /\ R e. ( SubGrp ` G ) ) /\ ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) ) -> ( ( Q .(+) R ) .(+) ( T .(+) U ) ) = ( ( Q .(+) T ) .(+) ( R .(+) U ) ) )

  proof
    cG
    cabl
    wcel
    #
    cQ
    cG
    csubg
    cfv
    #
    wcel
    #
    cR
    @1
    wcel
    #
    wa
    #
    cT
    @1
    wcel
    #
    cU
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cQ
    cR
    c.po
    co
    #
    cT
    c.po
    co
    #
    cU
    c.po
    co
    #
    cQ
    cT
    c.po
    co
    #
    cR
    c.po
    co
    #
    cU
    c.po
    co
    #
    @9
    cT
    cU
    c.po
    co
    c.po
    co
    #
    @12
    cR
    cU
    c.po
    co
    c.po
    co
    #
    @8
    @10
    @13
    cU
    c.po
    @8
    cQ
    cR
    cT
    c.po
    co
    #
    c.po
    co
    #
    cQ
    cT
    cR
    c.po
    co
    #
    c.po
    co
    #
    @10
    @13
    @8
    @17
    @19
    cQ
    c.po
    @8
    @0
    @3
    @5
    @17
    @19
    wceq
    @0
    @4
    @7
    simp1
    #
    @0
    @2
    @3
    @7
    simp2r
    #
    @0
    @4
    @5
    @6
    simp3l
    #
    c.po
    cR
    cT
    cG
    lsmcom.s
    lsmcom
    syl3anc
    oveq2d
    @8
    @2
    @3
    @5
    @10
    @18
    wceq
    @0
    @2
    @3
    @7
    simp2l
    #
    @22
    @23
    c.po
    cQ
    cR
    cT
    cG
    lsmcom.s
    lsmass
    syl3anc
    @8
    @2
    @5
    @3
    @13
    @20
    wceq
    @24
    @23
    @22
    c.po
    cQ
    cT
    cR
    cG
    lsmcom.s
    lsmass
    syl3anc
    3eqtr4d
    oveq1d
    @8
    @9
    @1
    wcel
    #
    @5
    @6
    @11
    @15
    wceq
    @8
    @0
    @2
    @3
    @25
    @21
    @24
    @22
    c.po
    cQ
    cR
    cG
    lsmcom.s
    lsmsubg2
    syl3anc
    @23
    @0
    @4
    @5
    @6
    simp3r
    #
    c.po
    @9
    cT
    cU
    cG
    lsmcom.s
    lsmass
    syl3anc
    @8
    @12
    @1
    wcel
    #
    @3
    @6
    @14
    @16
    wceq
    @8
    @0
    @2
    @5
    @27
    @21
    @24
    @23
    c.po
    cQ
    cT
    cG
    lsmcom.s
    lsmsubg2
    syl3anc
    @22
    @26
    c.po
    @12
    cR
    cU
    cG
    lsmcom.s
    lsmass
    syl3anc
    3eqtr3d
end
