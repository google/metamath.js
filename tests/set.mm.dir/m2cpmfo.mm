include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "m2cpmf.mm"
include "cc0.mm"
include "co.mm"
include "cco1.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cbs.mm"
include "eqid.mm"
include "simplll.mm"
include "simpllr.mm"
include "w3a.mm"
include "cpl1.mm"
include "cn0.mm"
include "cmat.mm"
include "simp2.mm"
include "simp3.mm"
include "cpmatpmat.mm"
include "3expa.mm"
include "adantlr.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "0nn0.mm"
include "coe1fvalcl.mm"
include "sylancl.mm"
include "matbas2d.mm"
include "fmptd.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "ccpmat2mat.mm"
include "cpm2mfval.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "m2cpminvid2.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem m2cpmfo
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vm: setvar m
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  assume m2cpmfo.s: |- S = ( N ConstPolyMat R )
  assume m2cpmfo.t: |- T = ( N matToPolyMat R )
  assume m2cpmfo.a: |- A = ( N Mat R )
  assume m2cpmfo.k: |- K = ( Base ` A )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> T : K -onto-> S )

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
    cK
    cS
    cT
    wf
    vx
    cv
    #
    vc
    cv
    #
    cT
    cfv
    #
    wceq
    #
    vc
    cK
    wrex
    #
    vx
    cS
    wral
    cK
    cS
    cT
    wfo
    cA
    cK
    cR
    cS
    cT
    cN
    m2cpmfo.s
    m2cpmfo.t
    m2cpmfo.a
    m2cpmfo.k
    m2cpmf
    @2
    @7
    vx
    cS
    @2
    @3
    cS
    wcel
    #
    wa
    #
    @6
    @3
    @3
    vm
    cS
    vi
    vj
    cN
    cN
    cc0
    vi
    cv
    #
    vj
    cv
    #
    vm
    cv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    cmpt
    #
    cfv
    #
    cT
    cfv
    #
    wceq
    #
    vc
    @18
    cK
    @9
    cS
    cK
    @3
    @17
    @9
    vm
    cS
    @16
    cK
    @17
    @9
    @12
    cS
    wcel
    #
    wa
    #
    vi
    vj
    cA
    cK
    @15
    cR
    cR
    cbs
    cfv
    #
    cN
    crg
    m2cpmfo.a
    @23
    eqid
    #
    m2cpmfo.k
    @0
    @1
    @8
    @21
    simplll
    @0
    @1
    @8
    @21
    simpllr
    @22
    @10
    cN
    wcel
    #
    @11
    cN
    wcel
    #
    w3a
    #
    @13
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    cc0
    cn0
    wcel
    @15
    @23
    wcel
    @27
    cN
    @28
    cmat
    co
    #
    @30
    cbs
    cfv
    #
    @28
    @10
    @11
    @29
    @12
    cN
    @30
    eqid
    #
    @29
    eqid
    #
    @31
    eqid
    #
    @22
    @25
    @26
    simp2
    @22
    @25
    @26
    simp3
    @22
    @25
    @12
    @31
    wcel
    #
    @26
    @2
    @21
    @35
    @8
    @0
    @1
    @21
    @35
    @31
    @30
    @28
    cR
    cS
    @12
    cN
    crg
    m2cpmfo.s
    @28
    eqid
    #
    @32
    @34
    cpmatpmat
    3expa
    adantlr
    3ad2ant1
    matecld
    0nn0
    @14
    @29
    @28
    cR
    @13
    @23
    cc0
    @14
    eqid
    @33
    @36
    @24
    coe1fvalcl
    sylancl
    matbas2d
    @17
    eqid
    fmptd
    @2
    @8
    simpr
    ffvelrnd
    @4
    @18
    wceq
    #
    @6
    @20
    wb
    @9
    @37
    @5
    @19
    @3
    @4
    @18
    cT
    fveq2
    eqeq2d
    adantl
    @9
    @19
    @3
    @0
    @1
    @8
    @19
    @3
    wceq
    @0
    @1
    @8
    w3a
    #
    @19
    @3
    cN
    cR
    ccpmat2mat
    co
    #
    cfv
    #
    cT
    cfv
    @3
    @38
    @18
    @40
    cT
    @38
    @40
    @18
    @0
    @1
    @40
    @18
    wceq
    @8
    @2
    @3
    @39
    @17
    vi
    vj
    cR
    cS
    vm
    @39
    cN
    crg
    @39
    eqid
    #
    m2cpmfo.s
    cpm2mfval
    fveq1d
    3adant3
    eqcomd
    fveq2d
    cR
    cS
    cT
    @39
    @3
    cN
    m2cpmfo.s
    @41
    m2cpmfo.t
    m2cpminvid2
    eqtrd
    3expa
    eqcomd
    rspcedvd
    ralrimiva
    vc
    vx
    cK
    cS
    cT
    dffo3
    sylanbrc
end
