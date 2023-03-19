include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "sspnv.mm"
include "nvf.mm"
include "syl.mm"
include "ffn.mm"
include "cba.mm"
include "cfv.mm"
include "wss.mm"
include "eqid.mm"
include "adantr.mm"
include "sspba.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "cv.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "ffun.mm"
include "funres.mm"
include "ad2antrr.mm"
include "fnresdm.mm"
include "cpv.mm"
include "cns.mm"
include "w3a.mm"
include "isssp.mm"
include "simplbda.mm"
include "simp3d.mm"
include "ssres.mm"
include "eqsstr3d.mm"
include "fdm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "sylan.mm"
include "funssfv.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "eqfnfvd.mm"

theorem sspn
  let cU: class U
  let cH: class H
  let cM: class M
  let cN: class N
  let cW: class W
  let cY: class Y
  let vx: setvar x
  assume sspn.y: |- Y = ( BaseSet ` W )
  assume sspn.n: |- N = ( normCV ` U )
  assume sspn.m: |- M = ( normCV ` W )
  assume sspn.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> M = ( N |` Y ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    vx
    cY
    cM
    cN
    cY
    cres
    #
    @2
    cY
    cr
    cM
    wf
    #
    cM
    cY
    wfn
    #
    @2
    cW
    cnv
    wcel
    #
    @4
    cU
    cH
    cW
    sspn.h
    sspnv
    #
    cW
    cM
    cY
    sspn.y
    sspn.m
    nvf
    #
    syl
    cY
    cr
    cM
    ffn
    syl
    #
    @2
    cN
    cU
    cba
    cfv
    #
    wfn
    #
    cY
    @10
    wss
    @3
    cY
    wfn
    @0
    @11
    @1
    @0
    @10
    cr
    cN
    wf
    #
    @11
    cU
    cN
    @10
    @10
    eqid
    #
    sspn.n
    nvf
    #
    @10
    cr
    cN
    ffn
    syl
    adantr
    cU
    cH
    cW
    @10
    cY
    @13
    sspn.y
    sspn.h
    sspba
    @10
    cY
    cN
    fnssres
    syl2anc
    @2
    vx
    cv
    #
    cY
    wcel
    #
    wa
    #
    @15
    @3
    cfv
    #
    @15
    cM
    cfv
    #
    @17
    @3
    wfun
    #
    cM
    @3
    wss
    #
    @15
    cM
    cdm
    #
    wcel
    #
    @18
    @19
    wceq
    @0
    @20
    @1
    @16
    @0
    cN
    wfun
    #
    @20
    @0
    @12
    @24
    @14
    @10
    cr
    cN
    ffun
    syl
    cY
    cN
    funres
    syl
    ad2antrr
    @2
    @21
    @16
    @2
    cM
    cM
    cY
    cres
    #
    @3
    @2
    @5
    @25
    cM
    wceq
    @9
    cY
    cM
    fnresdm
    syl
    @2
    cM
    cN
    wss
    #
    @25
    @3
    wss
    @2
    cW
    cpv
    cfv
    #
    cU
    cpv
    cfv
    #
    wss
    #
    cW
    cns
    cfv
    #
    cU
    cns
    cfv
    #
    wss
    #
    @26
    @0
    @1
    @6
    @29
    @32
    @26
    w3a
    @30
    @31
    cU
    @27
    @28
    cH
    cM
    cN
    cW
    @28
    eqid
    @27
    eqid
    @31
    eqid
    @30
    eqid
    sspn.n
    sspn.m
    sspn.h
    isssp
    simplbda
    simp3d
    cM
    cN
    cY
    ssres
    syl
    eqsstr3d
    adantr
    @2
    @6
    @16
    @23
    @7
    @6
    @23
    @16
    @6
    @22
    cY
    @15
    @6
    @4
    @22
    cY
    wceq
    @8
    cY
    cr
    cM
    fdm
    syl
    eleq2d
    biimpar
    sylan
    @15
    @3
    cM
    funssfv
    syl3anc
    eqcomd
    eqfnfvd
end
