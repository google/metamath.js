include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "unitcl.mm"
include "adantl.mm"
include "cinvr.mm"
include "oveq2.mm"
include "cur.mm"
include "unitlinv.mm"
include "adantr.mm"
include "oveq1d.mm"
include "simpll.mm"
include "ringinvcl.mm"
include "simpr.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "adantlr.mm"
include "3eqtr3d.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "ralrimiva.mm"
include "isrrg.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem unitrrg
  let cR: class R
  let cU: class U
  let cE: class E
  let vx: setvar x
  let vy: setvar y
  assume unitrrg.e: |- E = ( RLReg ` R )
  assume unitrrg.u: |- U = ( Unit ` R )


  assert |- ( R e. Ring -> U C_ E )

  proof
    cR
    crg
    wcel
    #
    vx
    cU
    cE
    @0
    vx
    cv
    #
    cU
    wcel
    #
    @1
    cE
    wcel
    #
    @0
    @2
    wa
    #
    @1
    cR
    cbs
    cfv
    #
    wcel
    #
    @1
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    @7
    @10
    wceq
    #
    wi
    #
    vy
    @5
    wral
    @3
    @2
    @6
    @0
    @5
    cR
    cU
    @1
    @5
    eqid
    #
    unitrrg.u
    unitcl
    adantl
    #
    @4
    @13
    vy
    @5
    @11
    @1
    cR
    cinvr
    cfv
    #
    cfv
    #
    @9
    @8
    co
    #
    @17
    @10
    @8
    co
    #
    wceq
    @4
    @7
    @5
    wcel
    #
    wa
    #
    @12
    @9
    @10
    @17
    @8
    oveq2
    @21
    @18
    @7
    @19
    @10
    @21
    @17
    @1
    @8
    co
    #
    @7
    @8
    co
    #
    cR
    cur
    cfv
    #
    @7
    @8
    co
    #
    @18
    @7
    @21
    @22
    @24
    @7
    @8
    @4
    @22
    @24
    wceq
    @20
    cR
    @8
    cU
    @24
    @16
    @1
    unitrrg.u
    @16
    eqid
    #
    @8
    eqid
    #
    @24
    eqid
    #
    unitlinv
    adantr
    oveq1d
    @21
    @0
    @17
    @5
    wcel
    #
    @6
    @20
    @23
    @18
    wceq
    @0
    @2
    @20
    simpll
    #
    @4
    @29
    @20
    @5
    cR
    cU
    @16
    @1
    unitrrg.u
    @26
    @14
    ringinvcl
    adantr
    #
    @4
    @6
    @20
    @15
    adantr
    @4
    @20
    simpr
    @5
    cR
    @8
    @17
    @1
    @7
    @14
    @27
    ringass
    syl13anc
    @0
    @20
    @25
    @7
    wceq
    @2
    @5
    cR
    @8
    @24
    @7
    @14
    @27
    @28
    ringlidm
    adantlr
    3eqtr3d
    @21
    @0
    @29
    @19
    @10
    wceq
    @30
    @31
    @5
    cR
    @8
    @17
    @10
    @14
    @27
    @10
    eqid
    #
    ringrz
    syl2anc
    eqeq12d
    syl5ib
    ralrimiva
    vy
    @5
    cR
    @8
    cE
    @1
    @10
    unitrrg.e
    @14
    @27
    @32
    isrrg
    sylanbrc
    ex
    ssrdv
end
