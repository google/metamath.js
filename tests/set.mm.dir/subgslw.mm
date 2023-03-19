include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cslw.mm"
include "co.mm"
include "wss.mm"
include "w3a.mm"
include "cprime.mm"
include "cv.mm"
include "cress.mm"
include "cpgp.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "slwprm.mm"
include "3ad2ant2.mm"
include "slwsubg.mm"
include "simp3.mm"
include "subsubg.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"
include "oveq1i.mm"
include "simpl1.mm"
include "simplbda.mm"
include "ressabs.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "simpl2.mm"
include "simprbda.mm"
include "eqid.mm"
include "slwispgp.mm"
include "bitrd.mm"
include "ralrimiva.mm"
include "isslw.mm"
include "syl3anbrc.mm"

theorem subgslw
  let cP: class P
  let cS: class S
  let cG: class G
  let cH: class H
  let cK: class K
  let vx: setvar x
  assume subgslw.1: |- H = ( G |`s S )


  assert |- ( ( S e. ( SubGrp ` G ) /\ K e. ( P pSyl G ) /\ K C_ S ) -> K e. ( P pSyl H ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cK
    cP
    cG
    cslw
    co
    wcel
    #
    cK
    cS
    wss
    #
    w3a
    #
    cP
    cprime
    wcel
    #
    cK
    cH
    csubg
    cfv
    #
    wcel
    #
    cK
    vx
    cv
    #
    wss
    #
    cP
    cH
    @8
    cress
    co
    #
    cpgp
    wbr
    #
    wa
    #
    cK
    @8
    wceq
    #
    wb
    #
    vx
    @6
    wral
    cK
    cP
    cH
    cslw
    co
    wcel
    @2
    @1
    @5
    @3
    cP
    cG
    cK
    slwprm
    3ad2ant2
    @4
    @7
    cK
    @0
    wcel
    #
    @3
    @2
    @1
    @15
    @3
    cP
    cG
    cK
    slwsubg
    3ad2ant2
    @1
    @2
    @3
    simp3
    @1
    @2
    @7
    @15
    @3
    wa
    wb
    @3
    cK
    cS
    cG
    cH
    subgslw.1
    subsubg
    3ad2ant1
    mpbir2and
    @4
    @14
    vx
    @6
    @4
    @8
    @6
    wcel
    #
    wa
    #
    @12
    @9
    cP
    cG
    @8
    cress
    co
    #
    cpgp
    wbr
    #
    wa
    #
    @13
    @17
    @11
    @19
    @9
    @17
    @10
    @18
    cP
    cpgp
    @17
    @10
    cG
    cS
    cress
    co
    #
    @8
    cress
    co
    #
    @18
    cH
    @21
    @8
    cress
    subgslw.1
    oveq1i
    @17
    @1
    @8
    cS
    wss
    #
    @22
    @18
    wceq
    @1
    @2
    @3
    @16
    simpl1
    @4
    @16
    @8
    @0
    wcel
    #
    @23
    @1
    @2
    @16
    @24
    @23
    wa
    wb
    @3
    @8
    cS
    cG
    cH
    subgslw.1
    subsubg
    3ad2ant1
    #
    simplbda
    cS
    @8
    cG
    @0
    ressabs
    syl2anc
    syl5eq
    breq2d
    anbi2d
    @17
    @2
    @24
    @20
    @13
    wb
    @1
    @2
    @3
    @16
    simpl2
    @4
    @16
    @24
    @23
    @25
    simprbda
    cP
    @18
    cG
    cK
    @8
    @18
    eqid
    slwispgp
    syl2anc
    bitrd
    ralrimiva
    cP
    vx
    cH
    cK
    isslw
    syl3anbrc
end
