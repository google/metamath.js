include "cn0.mm"
include "wcel.mm"
include "crelexp.mm"
include "co.mm"
include "crn.mm"
include "cdm.mm"
include "cun.mm"
include "wss.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "wa.mm"
include "relexpnnrn.mm"
include "ssun2.mm"
include "syl6ss.mm"
include "ex.mm"
include "cid.mm"
include "cres.mm"
include "simpl.mm"
include "oveq2d.mm"
include "relexp0g.mm"
include "adantl.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "rnresi.mm"
include "syl6eq.mm"
include "eqimss.mm"
include "syl.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"

theorem relexprng
  let cR: class R
  let cN: class N
  let cV: class V


  assert |- ( ( N e. NN0 /\ R e. V ) -> ran ( R ^r N ) C_ ( dom R u. ran R ) )

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
    crn
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
    @5
    @6
    cR
    cN
    cV
    relexpnnrn
    @5
    @4
    ssun2
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
    crn
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
    rneqd
    @6
    rnresi
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
