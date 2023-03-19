include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cmulr.mm"
include "co.mm"
include "crg.mm"
include "cbs.mm"
include "wceq.mm"
include "subrgrcl.mm"
include "adantr.mm"
include "wss.mm"
include "subrgbas.mm"
include "eqid.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "subrgring.mm"
include "ringinvcl.mm"
include "sylan.mm"
include "sseldd.mm"
include "unitcl.mm"
include "adantl.mm"
include "cui.mm"
include "subrguss.mm"
include "sselda.mm"
include "syldan.mm"
include "ringass.mm"
include "syl13anc.mm"
include "unitlinv.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "subrg1.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "unitrinv.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "ringridm.mm"

theorem subrginv
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cJ: class J
  let cX: class X
  assume subrginv.1: |- S = ( R |`s A )
  assume subrginv.2: |- I = ( invr ` R )
  assume subrginv.3: |- U = ( Unit ` S )
  assume subrginv.4: |- J = ( invr ` S )


  assert |- ( ( A e. ( SubRing ` R ) /\ X e. U ) -> ( I ` X ) = ( J ` X ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    #
    cR
    cur
    cfv
    #
    cX
    cI
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cX
    cJ
    cfv
    #
    @4
    @6
    co
    #
    @5
    @8
    @3
    @8
    cX
    @6
    co
    #
    @5
    @6
    co
    #
    @8
    cX
    @5
    @6
    co
    #
    @6
    co
    #
    @7
    @9
    @3
    cR
    crg
    wcel
    #
    @8
    cR
    cbs
    cfv
    #
    wcel
    #
    cX
    @15
    wcel
    @5
    @15
    wcel
    #
    @11
    @13
    wceq
    @1
    @14
    @2
    cA
    cR
    subrgrcl
    #
    adantr
    #
    @3
    cS
    cbs
    cfv
    #
    @15
    @8
    @1
    @20
    @15
    wss
    @2
    @1
    @20
    cA
    @15
    cA
    cR
    cS
    subrginv.1
    subrgbas
    cA
    @15
    cR
    @15
    eqid
    #
    subrgss
    eqsstr3d
    adantr
    #
    @1
    cS
    crg
    wcel
    #
    @2
    @8
    @20
    wcel
    cA
    cR
    cS
    subrginv.1
    subrgring
    #
    @20
    cS
    cU
    cJ
    cX
    subrginv.3
    subrginv.4
    @20
    eqid
    #
    ringinvcl
    sylan
    sseldd
    #
    @3
    @20
    @15
    cX
    @22
    @2
    cX
    @20
    wcel
    @1
    @20
    cS
    cU
    cX
    @25
    subrginv.3
    unitcl
    adantl
    sseldd
    @1
    @2
    cX
    cR
    cui
    cfv
    #
    wcel
    #
    @17
    @1
    cU
    @27
    cX
    cA
    cR
    cS
    @27
    cU
    subrginv.1
    @27
    eqid
    #
    subrginv.3
    subrguss
    sselda
    #
    @1
    @14
    @28
    @17
    @18
    @15
    cR
    @27
    cI
    cX
    @29
    subrginv.2
    @21
    ringinvcl
    sylan
    syldan
    #
    @15
    cR
    @6
    @8
    cX
    @5
    @21
    @6
    eqid
    #
    ringass
    syl13anc
    @3
    @10
    @4
    @5
    @6
    @3
    @8
    cX
    cS
    cmulr
    cfv
    #
    co
    #
    cS
    cur
    cfv
    #
    @10
    @4
    @1
    @23
    @2
    @34
    @35
    wceq
    @24
    cS
    @33
    cU
    @35
    cJ
    cX
    subrginv.3
    subrginv.4
    @33
    eqid
    @35
    eqid
    unitlinv
    sylan
    @3
    @6
    @33
    @8
    cX
    @1
    @6
    @33
    wceq
    @2
    cA
    cR
    cS
    @6
    @0
    subrginv.1
    @32
    ressmulr
    adantr
    oveqd
    @1
    @4
    @35
    wceq
    @2
    cA
    cR
    cS
    @4
    subrginv.1
    @4
    eqid
    #
    subrg1
    adantr
    3eqtr4d
    oveq1d
    @3
    @12
    @4
    @8
    @6
    @1
    @2
    @28
    @12
    @4
    wceq
    #
    @30
    @1
    @14
    @28
    @37
    @18
    cR
    @6
    @27
    @4
    cI
    cX
    @29
    subrginv.2
    @32
    @36
    unitrinv
    sylan
    syldan
    oveq2d
    3eqtr3d
    @3
    @14
    @17
    @7
    @5
    wceq
    @19
    @31
    @15
    cR
    @6
    @4
    @5
    @21
    @32
    @36
    ringlidm
    syl2anc
    @3
    @14
    @16
    @9
    @8
    wceq
    @19
    @26
    @15
    cR
    @6
    @4
    @8
    @21
    @32
    @36
    ringridm
    syl2anc
    3eqtr3d
end
