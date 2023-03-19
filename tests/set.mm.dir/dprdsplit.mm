include "cdprd.mm"
include "co.mm"
include "cres.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "wcel.mm"
include "ccntz.mm"
include "wss.mm"
include "wbr.mm"
include "cun.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "dprdres.mm"
include "simpld.mm"
include "dprdsubg.mm"
include "ssun2.mm"
include "wa.mm"
include "cin.mm"
include "c0g.mm"
include "csn.mm"
include "w3a.mm"
include "eqid.mm"
include "dmdprdsplit.mm"
include "mpbid.mm"
include "simp2d.mm"
include "lsmsubg.mm"
include "syl3anc.mm"
include "cv.mm"
include "wo.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "fvres.mm"
include "adantl.mm"
include "adantr.mm"
include "fssresd.mm"
include "simpr.mm"
include "dprdub.mm"
include "eqsstr3d.mm"
include "lsmub1.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "lsmub2.mm"
include "jaodan.mm"
include "syldan.mm"
include "dprdlub.mm"
include "simprd.mm"
include "wb.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "eqssd.mm"

theorem dprdsplit
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.po: class .(+)
  let cS: class S
  let cG: class G
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cZ: class Z
  assume dprdsplit.2: |- ( ph -> S : I --> ( SubGrp ` G ) )
  assume dprdsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume dprdsplit.u: |- ( ph -> I = ( C u. D ) )
  assume dprdsplit.s: |- .(+) = ( LSSum ` G )
  assume dprdsplit.1: |- ( ph -> G dom DProd S )


  assert |- ( ph -> ( G DProd S ) = ( ( G DProd ( S |` C ) ) .(+) ( G DProd ( S |` D ) ) ) )

  proof
    wph
    cG
    cS
    cdprd
    co
    #
    cG
    cS
    cC
    cres
    #
    cdprd
    co
    #
    cG
    cS
    cD
    cres
    #
    cdprd
    co
    #
    c.po
    co
    #
    wph
    cS
    @5
    vx
    cG
    cI
    dprdsplit.1
    wph
    cI
    cG
    csubg
    cfv
    #
    cS
    wf
    cS
    cdm
    cI
    wceq
    dprdsplit.2
    cI
    @6
    cS
    fdm
    syl
    #
    wph
    @2
    @6
    wcel
    #
    @4
    @6
    wcel
    #
    @2
    @4
    cG
    ccntz
    cfv
    #
    cfv
    wss
    #
    @5
    @6
    wcel
    wph
    cG
    @1
    cdprd
    cdm
    #
    wbr
    #
    @8
    wph
    @13
    @2
    @0
    wss
    #
    wph
    cC
    cS
    cG
    cI
    dprdsplit.1
    @7
    wph
    cC
    cD
    cun
    #
    cC
    cI
    cC
    cD
    ssun1
    dprdsplit.u
    syl5sseqr
    #
    dprdres
    #
    simpld
    #
    @1
    cG
    dprdsubg
    syl
    #
    wph
    cG
    @3
    @12
    wbr
    #
    @9
    wph
    @20
    @4
    @0
    wss
    #
    wph
    cD
    cS
    cG
    cI
    dprdsplit.1
    @7
    wph
    @15
    cD
    cI
    cD
    cC
    ssun2
    dprdsplit.u
    syl5sseqr
    #
    dprdres
    #
    simpld
    #
    @3
    cG
    dprdsubg
    syl
    #
    wph
    @13
    @20
    wa
    #
    @11
    @2
    @4
    cin
    cG
    c0g
    cfv
    #
    csn
    wceq
    #
    wph
    cG
    cS
    @12
    wbr
    #
    @26
    @11
    @28
    w3a
    dprdsplit.1
    wph
    cC
    cD
    cS
    cG
    cI
    @27
    @10
    dprdsplit.2
    dprdsplit.i
    dprdsplit.u
    @10
    eqid
    #
    @27
    eqid
    dmdprdsplit
    mpbid
    simp2d
    c.po
    @2
    @4
    cG
    @10
    dprdsplit.s
    @30
    lsmsubg
    syl3anc
    wph
    vx
    cv
    #
    cI
    wcel
    #
    @31
    cC
    wcel
    #
    @31
    cD
    wcel
    #
    wo
    #
    @31
    cS
    cfv
    #
    @5
    wss
    #
    wph
    @32
    @35
    wph
    @32
    @31
    @15
    wcel
    @35
    wph
    cI
    @15
    @31
    dprdsplit.u
    eleq2d
    @31
    cC
    cD
    elun
    syl6bb
    biimpa
    wph
    @33
    @37
    @34
    wph
    @33
    wa
    #
    @36
    @2
    @5
    @38
    @36
    @31
    @1
    cfv
    #
    @2
    @33
    @39
    @36
    wceq
    wph
    @31
    cC
    cS
    fvres
    adantl
    @38
    @1
    cG
    cC
    @31
    wph
    @13
    @33
    @18
    adantr
    wph
    @1
    cdm
    cC
    wceq
    #
    @33
    wph
    cC
    @6
    @1
    wf
    @40
    wph
    cI
    @6
    cC
    cS
    dprdsplit.2
    @16
    fssresd
    cC
    @6
    @1
    fdm
    syl
    adantr
    wph
    @33
    simpr
    dprdub
    eqsstr3d
    wph
    @2
    @5
    wss
    #
    @33
    wph
    @8
    @9
    @41
    @19
    @25
    c.po
    @2
    @4
    cG
    dprdsplit.s
    lsmub1
    syl2anc
    adantr
    sstrd
    wph
    @34
    wa
    #
    @36
    @4
    @5
    @42
    @36
    @31
    @3
    cfv
    #
    @4
    @34
    @43
    @36
    wceq
    wph
    @31
    cD
    cS
    fvres
    adantl
    @42
    @3
    cG
    cD
    @31
    wph
    @20
    @34
    @24
    adantr
    wph
    @3
    cdm
    cD
    wceq
    #
    @34
    wph
    cD
    @6
    @3
    wf
    @44
    wph
    cI
    @6
    cD
    cS
    dprdsplit.2
    @22
    fssresd
    cD
    @6
    @3
    fdm
    syl
    adantr
    wph
    @34
    simpr
    dprdub
    eqsstr3d
    wph
    @4
    @5
    wss
    #
    @34
    wph
    @8
    @9
    @45
    @19
    @25
    c.po
    @2
    @4
    cG
    dprdsplit.s
    lsmub2
    syl2anc
    adantr
    sstrd
    jaodan
    syldan
    dprdlub
    wph
    @14
    @21
    @5
    @0
    wss
    #
    wph
    @13
    @14
    @17
    simprd
    wph
    @20
    @21
    @23
    simprd
    wph
    @8
    @9
    @0
    @6
    wcel
    #
    @14
    @21
    wa
    @46
    wb
    @19
    @25
    wph
    @29
    @47
    dprdsplit.1
    cS
    cG
    dprdsubg
    syl
    c.po
    @2
    @4
    @0
    cG
    dprdsplit.s
    lsmlub
    syl3anc
    mpbi2and
    eqssd
end
