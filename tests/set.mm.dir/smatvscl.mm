include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "eqid.mm"
include "scmatel.mm"
include "oveq2.mm"
include "adantl.mm"
include "csca.mm"
include "cmulr.mm"
include "clmod.mm"
include "matlmod.mm"
include "ad3antrrr.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ad2antrr.mm"
include "matring.mm"
include "ringidcl.mm"
include "syl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "simplll.mm"
include "adantr.mm"
include "oveqd.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "rspcedeq2vd.mm"
include "wb.mm"
include "mpbir2and.mm"
include "ex.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "com23.mm"
include "sylbid.mm"
include "imp32.mm"

theorem smatvscl
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let c.as: class .*
  let cK: class K
  let cN: class N
  let cX: class X
  let vc: setvar c
  let ve: setvar e
  assume smatvscl.k: |- K = ( Base ` R )
  assume smatvscl.a: |- A = ( N Mat R )
  assume smatvscl.s: |- S = ( N ScMat R )
  assume smatvscl.t: |- .* = ( .s ` A )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( C e. K /\ X e. S ) ) -> ( C .* X ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cC
    cK
    wcel
    #
    cX
    cS
    wcel
    #
    cC
    cX
    c.as
    co
    #
    cS
    wcel
    #
    @2
    @4
    @3
    @6
    @2
    @4
    cX
    cA
    cbs
    cfv
    #
    wcel
    #
    cX
    vc
    cv
    #
    cA
    cur
    cfv
    #
    c.as
    co
    #
    wceq
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    wa
    #
    @3
    @6
    wi
    cA
    @7
    cR
    cS
    c.as
    @10
    @13
    cX
    cN
    crg
    vc
    @13
    eqid
    smatvscl.a
    @7
    eqid
    #
    @10
    eqid
    #
    smatvscl.t
    smatvscl.s
    scmatel
    @2
    @3
    @15
    @6
    @2
    @3
    @15
    @6
    wi
    @2
    @3
    wa
    #
    @8
    @14
    @6
    @18
    @8
    wa
    #
    @12
    @6
    vc
    @13
    @19
    @9
    @13
    wcel
    #
    wa
    #
    @12
    @6
    @21
    @12
    wa
    @5
    cC
    @11
    c.as
    co
    #
    cS
    @12
    @5
    @22
    wceq
    @21
    cX
    @11
    cC
    c.as
    oveq2
    adantl
    @21
    @22
    cS
    wcel
    @12
    @21
    @22
    cC
    @9
    cA
    csca
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    @10
    c.as
    co
    #
    cS
    @21
    @26
    @22
    @21
    cA
    clmod
    wcel
    #
    cC
    @23
    cbs
    cfv
    #
    wcel
    #
    @9
    @28
    wcel
    #
    @10
    @7
    wcel
    #
    @26
    @22
    wceq
    @2
    @27
    @3
    @8
    @20
    cA
    cR
    cN
    smatvscl.a
    matlmod
    ad3antrrr
    @18
    @29
    @8
    @20
    @2
    @3
    @29
    @2
    cK
    @28
    cC
    @2
    cK
    @13
    @28
    smatvscl.k
    @2
    cR
    @23
    cbs
    cA
    cR
    cN
    crg
    smatvscl.a
    matsca2
    #
    fveq2d
    syl5eq
    eleq2d
    biimpa
    ad2antrr
    @19
    @20
    @30
    @19
    @13
    @28
    @9
    @19
    cR
    @23
    cbs
    @2
    cR
    @23
    wceq
    #
    @3
    @8
    @32
    ad2antrr
    fveq2d
    eleq2d
    biimpa
    @2
    @31
    @3
    @8
    @20
    @2
    cA
    crg
    wcel
    @31
    cA
    cR
    cN
    smatvscl.a
    matring
    @7
    cA
    @10
    @16
    @17
    ringidcl
    syl
    ad3antrrr
    #
    cC
    @9
    c.as
    @24
    @23
    @28
    @7
    cA
    @10
    @16
    @23
    eqid
    smatvscl.t
    @28
    eqid
    @24
    eqid
    lmodvsass
    syl13anc
    eqcomd
    @21
    @26
    cS
    wcel
    #
    @26
    @7
    wcel
    #
    @26
    ve
    cv
    #
    @10
    c.as
    co
    #
    wceq
    #
    ve
    cK
    wrex
    #
    @21
    @2
    @25
    cK
    wcel
    @31
    @36
    @2
    @3
    @8
    @20
    simplll
    @21
    @25
    cC
    @9
    cR
    cmulr
    cfv
    #
    co
    #
    cK
    @21
    @24
    @41
    cC
    @9
    @21
    @23
    cR
    cmulr
    @18
    @23
    cR
    wceq
    @8
    @20
    @18
    cR
    @23
    @2
    @33
    @3
    @32
    adantr
    eqcomd
    ad2antrr
    fveq2d
    oveqd
    @21
    @1
    @3
    @9
    cK
    wcel
    #
    @42
    cK
    wcel
    @0
    @1
    @3
    @8
    @20
    simp-4r
    @2
    @3
    @8
    @20
    simpllr
    @20
    @43
    @19
    @20
    @43
    @13
    cK
    @9
    cK
    @13
    smatvscl.k
    eqcomi
    eleq2i
    biimpi
    adantl
    cK
    cR
    @41
    cC
    @9
    smatvscl.k
    @41
    eqid
    ringcl
    syl3anc
    eqeltrd
    #
    @34
    cA
    @7
    @25
    cR
    c.as
    cK
    cN
    @10
    smatvscl.k
    smatvscl.a
    @16
    smatvscl.t
    matvscl
    syl12anc
    @21
    ve
    @25
    cK
    @26
    @38
    @44
    @37
    @25
    wceq
    @39
    @21
    @39
    @25
    @37
    @25
    @37
    @10
    c.as
    oveq1
    eqcoms
    adantl
    rspcedeq2vd
    @2
    @35
    @36
    @40
    wa
    wb
    @3
    @8
    @20
    cA
    @7
    cR
    cS
    c.as
    @10
    cK
    @26
    cN
    crg
    ve
    smatvscl.k
    smatvscl.a
    @16
    @17
    smatvscl.t
    smatvscl.s
    scmatel
    ad3antrrr
    mpbir2and
    eqeltrd
    adantr
    eqeltrd
    ex
    rexlimdva
    expimpd
    ex
    com23
    sylbid
    com23
    imp32
end
