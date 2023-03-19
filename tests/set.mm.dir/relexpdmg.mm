include "cn0.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wss.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "wa.mm"
include "relexpnndm.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "ex.mm"
include "cid.mm"
include "cres.mm"
include "simpl.mm"
include "oveq2d.mm"
include "relexp0g.mm"
include "adantl.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "dmresi.mm"
include "syl6eq.mm"
include "eqimss.mm"
include "syl.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"

theorem relexpdmg
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN0 /\ R e. V ) -> dom ( R ^r N ) C_ ( dom R u. ran R ) )

  proof
    cN
    cn0
    wcel
    #
    cR
    cV
    wcel
    #
    cR
    cN
    crelexp
    co
    #
    cdm
    #
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    wss
    #
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
    @7
    @8
    @1
    wa
    @3
    @4
    @6
    cR
    cN
    cV
    relexpnndm
    @4
    @5
    ssun1
    syl6ss
    ex
    @9
    @1
    @7
    @9
    @1
    wa
    #
    @3
    @6
    wceq
    @7
    @11
    @3
    cid
    @6
    cres
    #
    cdm
    @6
    @11
    @2
    @12
    @11
    @2
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
    simpl
    oveq2d
    @1
    @13
    @12
    wceq
    @9
    cR
    cV
    relexp0g
    adantl
    eqtrd
    dmeqd
    @6
    dmresi
    syl6eq
    @3
    @6
    eqimss
    syl
    ex
    jaoi
    sylbi
    imp
end
