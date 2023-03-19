include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "simpr.mm"
include "eqid.mm"
include "isunit.mm"
include "sylib.mm"
include "simpld.mm"
include "wceq.mm"
include "subrg1.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "wss.mm"
include "subrgdvds.mm"
include "ssbrd.mm"
include "mpd.mm"
include "cinvr.mm"
include "cmulr.mm"
include "co.mm"
include "cbs.mm"
include "subrgbas.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "unitcl.mm"
include "adantl.mm"
include "sseldd.mm"
include "crg.mm"
include "subrgring.mm"
include "ringinvcl.mm"
include "sylan.mm"
include "opprbas.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "opprmul.mm"
include "unitrinv.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "3eqtr4d.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem subrguss
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let cV: class V
  let vx: setvar x
  assume subrguss.1: |- S = ( R |`s A )
  assume subrguss.2: |- U = ( Unit ` R )
  assume subrguss.3: |- V = ( Unit ` S )


  assert |- ( A e. ( SubRing ` R ) -> V C_ U )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    vx
    cV
    cU
    @1
    vx
    cv
    #
    cV
    wcel
    #
    @2
    cU
    wcel
    #
    @1
    @3
    wa
    #
    @2
    cR
    cur
    cfv
    #
    cR
    cdsr
    cfv
    #
    wbr
    #
    @2
    @6
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    @4
    @5
    @2
    @6
    cS
    cdsr
    cfv
    #
    wbr
    @8
    @5
    @2
    cS
    cur
    cfv
    #
    @6
    @11
    @5
    @2
    @12
    @11
    wbr
    #
    @2
    @12
    cS
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    @5
    @3
    @13
    @16
    wa
    @1
    @3
    simpr
    @11
    cS
    @14
    cV
    @12
    @15
    @2
    subrguss.3
    @12
    eqid
    #
    @11
    eqid
    #
    @14
    eqid
    @15
    eqid
    isunit
    sylib
    simpld
    @1
    @6
    @12
    wceq
    @3
    cA
    cR
    cS
    @6
    subrguss.1
    @6
    eqid
    #
    subrg1
    adantr
    #
    breqtrrd
    @5
    @11
    @7
    @2
    @6
    @1
    @11
    @7
    wss
    @3
    cA
    @7
    cR
    cS
    @11
    subrguss.1
    @7
    eqid
    #
    @18
    subrgdvds
    adantr
    ssbrd
    mpd
    @5
    @2
    @2
    cS
    cinvr
    cfv
    #
    cfv
    #
    @2
    @9
    cmulr
    cfv
    #
    co
    #
    @6
    @10
    @5
    @2
    cR
    cbs
    cfv
    #
    wcel
    @23
    @26
    wcel
    @2
    @25
    @10
    wbr
    @5
    cS
    cbs
    cfv
    #
    @26
    @2
    @5
    @27
    cA
    @26
    @1
    cA
    @27
    wceq
    @3
    cA
    cR
    cS
    subrguss.1
    subrgbas
    adantr
    @1
    cA
    @26
    wss
    @3
    cA
    @26
    cR
    @26
    eqid
    #
    subrgss
    adantr
    eqsstr3d
    #
    @3
    @2
    @27
    wcel
    @1
    @27
    cS
    cV
    @2
    @27
    eqid
    #
    subrguss.3
    unitcl
    adantl
    sseldd
    @5
    @27
    @26
    @23
    @29
    @1
    cS
    crg
    wcel
    #
    @3
    @23
    @27
    wcel
    cA
    cR
    cS
    subrguss.1
    subrgring
    #
    @27
    cS
    cV
    @22
    @2
    subrguss.3
    @22
    eqid
    #
    @30
    ringinvcl
    sylan
    sseldd
    @26
    @10
    @9
    @24
    @2
    @23
    @26
    cR
    @9
    @9
    eqid
    #
    @28
    opprbas
    @10
    eqid
    #
    @24
    eqid
    #
    dvdsrmul
    syl2anc
    @5
    @25
    @2
    @23
    cR
    cmulr
    cfv
    #
    co
    #
    @6
    @26
    cR
    @24
    @37
    @9
    @23
    @2
    @28
    @37
    eqid
    #
    @34
    @36
    opprmul
    @5
    @2
    @23
    cS
    cmulr
    cfv
    #
    co
    #
    @12
    @38
    @6
    @1
    @31
    @3
    @41
    @12
    wceq
    @32
    cS
    @40
    cV
    @12
    @22
    @2
    subrguss.3
    @33
    @40
    eqid
    @17
    unitrinv
    sylan
    @5
    @37
    @40
    @2
    @23
    @1
    @37
    @40
    wceq
    @3
    cA
    cR
    cS
    @37
    @0
    subrguss.1
    @39
    ressmulr
    adantr
    oveqd
    @20
    3eqtr4d
    syl5eq
    breqtrd
    @7
    cR
    @9
    cU
    @6
    @10
    @2
    subrguss.2
    @19
    @21
    @34
    @35
    isunit
    sylanbrc
    ex
    ssrdv
end
