include "cedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "ciedg.mm"
include "crn.mm"
include "edgval.mm"
include "eleq2i.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "wfun.mm"
include "wb.mm"
include "cres.mm"
include "cuhgr.mm"
include "uhgrfun.mm"
include "funres.mm"
include "3syl.mm"
include "funeqd.mm"
include "mpbird.mm"
include "elrnrexdmb.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "fveq1d.mm"
include "cin.mm"
include "dmeqd.mm"
include "dmres.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "elinel1.mm"
include "syl6bi.mm"
include "imp.mm"
include "fvresd.mm"
include "eqtrd.mm"
include "wss.mm"
include "elinel2.mm"
include "uhgrss.mm"
include "syl2an2r.mm"
include "pweqd.mm"
include "fvex.mm"
include "elpw.mm"
include "syl6bb.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem uhgrspansubgrlem
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vi: setvar i
  assume uhgrspan.v: |- V = ( Vtx ` G )
  assume uhgrspan.e: |- E = ( iEdg ` G )
  assume uhgrspan.s: |- ( ph -> S e. W )
  assume uhgrspan.q: |- ( ph -> ( Vtx ` S ) = V )
  assume uhgrspan.r: |- ( ph -> ( iEdg ` S ) = ( E |` A ) )
  assume uhgrspan.g: |- ( ph -> G e. UHGraph )


  assert |- ( ph -> ( Edg ` S ) C_ ~P ( Vtx ` S ) )

  proof
    wph
    ve
    cS
    cedg
    cfv
    #
    cS
    cvtx
    cfv
    #
    cpw
    #
    ve
    cv
    #
    @0
    wcel
    @3
    cS
    ciedg
    cfv
    #
    crn
    #
    wcel
    #
    wph
    @3
    @2
    wcel
    #
    @0
    @5
    @3
    cS
    edgval
    eleq2i
    wph
    @6
    @3
    vi
    cv
    #
    @4
    cfv
    #
    wceq
    #
    vi
    @4
    cdm
    #
    wrex
    #
    @7
    wph
    @4
    wfun
    #
    @6
    @12
    wb
    wph
    @13
    cE
    cA
    cres
    #
    wfun
    #
    wph
    cG
    cuhgr
    wcel
    #
    cE
    wfun
    @15
    uhgrspan.g
    cE
    cG
    uhgrspan.e
    uhgrfun
    cA
    cE
    funres
    3syl
    wph
    @4
    @14
    uhgrspan.r
    funeqd
    mpbird
    vi
    @4
    @3
    elrnrexdmb
    syl
    wph
    @10
    @7
    vi
    @11
    wph
    @8
    @11
    wcel
    #
    wa
    #
    @7
    @10
    @9
    @2
    wcel
    @18
    @9
    @8
    cE
    cfv
    #
    @2
    @18
    @9
    @8
    @14
    cfv
    @19
    @18
    @8
    @4
    @14
    wph
    @4
    @14
    wceq
    @17
    uhgrspan.r
    adantr
    fveq1d
    @18
    @8
    cA
    cE
    wph
    @17
    @8
    cA
    wcel
    #
    wph
    @17
    @8
    cA
    cE
    cdm
    #
    cin
    #
    wcel
    #
    @20
    wph
    @11
    @22
    @8
    wph
    @11
    @14
    cdm
    @22
    wph
    @4
    @14
    uhgrspan.r
    dmeqd
    cE
    cA
    dmres
    syl6eq
    eleq2d
    #
    @8
    cA
    @21
    elinel1
    syl6bi
    imp
    fvresd
    eqtrd
    @18
    @19
    @2
    wcel
    #
    @19
    cV
    wss
    #
    wph
    @16
    @17
    @8
    @21
    wcel
    #
    @26
    uhgrspan.g
    wph
    @17
    @27
    wph
    @17
    @23
    @27
    @24
    @8
    cA
    @21
    elinel2
    syl6bi
    imp
    cE
    @8
    cG
    cV
    uhgrspan.v
    uhgrspan.e
    uhgrss
    syl2an2r
    @18
    @25
    @19
    cV
    cpw
    #
    wcel
    #
    @26
    wph
    @25
    @29
    wb
    @17
    wph
    @2
    @28
    @19
    wph
    @1
    cV
    uhgrspan.q
    pweqd
    eleq2d
    adantr
    @19
    cV
    @8
    cE
    fvex
    elpw
    syl6bb
    mpbird
    eqeltrd
    @3
    @9
    @2
    eleq1
    syl5ibrcom
    rexlimdva
    sylbid
    syl5bi
    ssrdv
end
