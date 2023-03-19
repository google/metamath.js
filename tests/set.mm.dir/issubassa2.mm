include "casa.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "cur.mm"
include "csn.mm"
include "clspn.mm"
include "wceq.mm"
include "eqid.mm"
include "rnascl.mm"
include "ad2antrr.mm"
include "clmod.mm"
include "assalmod.mm"
include "simpr.mm"
include "subrg1cl.mm"
include "ad2antlr.mm"
include "lspsnel5a.mm"
include "eqsstrd.mm"
include "csubg.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "subrgsubg.mm"
include "cmulr.mm"
include "simplll.mm"
include "simprl.mm"
include "subrgss.mm"
include "sselda.mm"
include "adantrl.mm"
include "asclmul1.mm"
include "syl3anc.mm"
include "simpllr.mm"
include "simplr.mm"
include "wfn.mm"
include "asclfn.mm"
include "a1i.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseldd.mm"
include "adantrr.mm"
include "simprr.mm"
include "subrgmcl.mm"
include "eqeltrrd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "islss4.mm"
include "syl.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem issubassa2
  let cA: class A
  let cS: class S
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume issubassa2.a: |- A = ( algSc ` W )
  assume issubassa2.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. AssAlg /\ S e. ( SubRing ` W ) ) -> ( S e. L <-> ran A C_ S ) )

  proof
    cW
    casa
    wcel
    #
    cS
    cW
    csubrg
    cfv
    wcel
    #
    wa
    #
    cS
    cL
    wcel
    #
    cA
    crn
    #
    cS
    wss
    #
    @2
    @3
    wa
    #
    @4
    cW
    cur
    cfv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    cS
    @0
    @4
    @9
    wceq
    @1
    @3
    cA
    @7
    @8
    cW
    issubassa2.a
    @7
    eqid
    #
    @8
    eqid
    #
    rnascl
    ad2antrr
    @6
    cL
    cS
    @8
    cW
    @7
    issubassa2.l
    @11
    @0
    cW
    clmod
    wcel
    #
    @1
    @3
    cW
    assalmod
    #
    ad2antrr
    @2
    @3
    simpr
    @1
    @7
    cS
    wcel
    @0
    @3
    cS
    cW
    @7
    @10
    subrg1cl
    ad2antlr
    lspsnel5a
    eqsstrd
    @2
    @5
    wa
    #
    @3
    cS
    cW
    csubg
    cfv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    @1
    @15
    @0
    @5
    cS
    cW
    subrgsubg
    ad2antlr
    @14
    @20
    vx
    vy
    @22
    cS
    @14
    @16
    @22
    wcel
    #
    @17
    cS
    wcel
    #
    wa
    #
    wa
    #
    @16
    cA
    cfv
    #
    @17
    cW
    cmulr
    cfv
    #
    co
    #
    @19
    cS
    @27
    @0
    @24
    @17
    cW
    cbs
    cfv
    #
    wcel
    #
    @30
    @19
    wceq
    @0
    @1
    @5
    @26
    simplll
    @14
    @24
    @25
    simprl
    @14
    @25
    @32
    @24
    @14
    cS
    @31
    @17
    @1
    cS
    @31
    wss
    @0
    @5
    cS
    @31
    cW
    @31
    eqid
    #
    subrgss
    ad2antlr
    sselda
    adantrl
    cA
    @16
    @18
    @29
    @21
    @22
    @31
    cW
    @17
    issubassa2.a
    @21
    eqid
    #
    @22
    eqid
    #
    @33
    @29
    eqid
    #
    @18
    eqid
    #
    asclmul1
    syl3anc
    @27
    @1
    @28
    cS
    wcel
    #
    @25
    @30
    cS
    wcel
    @0
    @1
    @5
    @26
    simpllr
    @14
    @24
    @38
    @25
    @14
    @24
    wa
    @4
    cS
    @28
    @2
    @5
    @24
    simplr
    @14
    cA
    @22
    wfn
    #
    @24
    @28
    @4
    wcel
    @39
    @14
    cA
    @21
    @22
    cW
    issubassa2.a
    @34
    @35
    asclfn
    a1i
    @22
    @16
    cA
    fnfvelrn
    sylan
    sseldd
    adantrr
    @14
    @24
    @25
    simprr
    cS
    cW
    @29
    @28
    @17
    @36
    subrgmcl
    syl3anc
    eqeltrrd
    ralrimivva
    @0
    @3
    @15
    @23
    wa
    wb
    #
    @1
    @5
    @0
    @12
    @40
    @13
    @22
    cL
    @18
    cS
    @21
    @31
    cW
    vx
    vy
    @34
    @35
    @33
    @37
    issubassa2.l
    islss4
    syl
    ad2antrr
    mpbir2and
    impbida
end
