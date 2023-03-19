include "cn0.mm"
include "wcel.mm"
include "wrel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crelexp.mm"
include "ccom.mm"
include "wceq.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "elnn0.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "relexpsucnnl.mm"
include "syl2anc.mm"
include "3expib.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "simp2.mm"
include "relcoi1.mm"
include "syl.mm"
include "oveq2d.mm"
include "relexp0.mm"
include "eqtrd.mm"
include "coeq2d.mm"
include "oveq1d.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "relexp1g.mm"
include "3eqtr4rd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3impib.mm"
include "3com13.mm"

theorem relexpsucl
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( R e. V /\ Rel R /\ N e. NN0 ) -> ( R ^r ( N + 1 ) ) = ( R o. ( R ^r N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cR
    wrel
    #
    cR
    cV
    wcel
    #
    cR
    cN
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cR
    cN
    crelexp
    co
    #
    ccom
    #
    wceq
    #
    @0
    @1
    @2
    @7
    @0
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @1
    @2
    wa
    @7
    wi
    #
    cN
    elnn0
    @8
    @10
    @9
    @8
    @1
    @2
    @7
    @8
    @1
    @2
    w3a
    @2
    @8
    @7
    @8
    @1
    @2
    simp3
    @8
    @1
    @2
    simp1
    cR
    cN
    cV
    relexpsucnnl
    syl2anc
    3expib
    @9
    @1
    @2
    @7
    @9
    @1
    @2
    w3a
    #
    cR
    cid
    cR
    cuni
    cuni
    cres
    #
    ccom
    #
    cR
    @6
    @4
    @11
    @1
    @13
    cR
    wceq
    @9
    @1
    @2
    simp2
    #
    cR
    relcoi1
    syl
    @11
    @5
    @12
    cR
    @11
    @5
    cR
    cc0
    crelexp
    co
    #
    @12
    @11
    cN
    cc0
    cR
    crelexp
    @9
    @1
    @2
    simp1
    #
    oveq2d
    @11
    @2
    @1
    @15
    @12
    wceq
    @9
    @1
    @2
    simp3
    #
    @14
    cR
    cV
    relexp0
    syl2anc
    eqtrd
    coeq2d
    @11
    @4
    cR
    c1
    crelexp
    co
    #
    cR
    @11
    @3
    c1
    cR
    crelexp
    @11
    @3
    cc0
    c1
    caddc
    co
    c1
    @11
    cN
    cc0
    c1
    caddc
    @16
    oveq1d
    0p1e1
    syl6eq
    oveq2d
    @11
    @2
    @18
    cR
    wceq
    @17
    cR
    cV
    relexp1g
    syl
    eqtrd
    3eqtr4rd
    3expib
    jaoi
    sylbi
    3impib
    3com13
end
