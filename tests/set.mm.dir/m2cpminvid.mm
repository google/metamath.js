include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cmpt2.mm"
include "ccpmat.mm"
include "wceq.mm"
include "eqid.mm"
include "m2cpm.mm"
include "cpm2mval.mm"
include "syld3an3.mm"
include "cpl1.mm"
include "cascl.mm"
include "mat2pmatvalel.mm"
include "3impb.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cbs.mm"
include "simp12.mm"
include "simp2.mm"
include "simp3.mm"
include "simp13.mm"
include "matecld.mm"
include "ply1sclid.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "mpt2eq3dva.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "eqidd.mm"
include "oveq12.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "ralrimivva.mm"
include "wb.mm"
include "simp1.mm"
include "matbas2d.mm"
include "eqmat.mm"
include "mpbird.mm"
include "3eqtrd.mm"

theorem m2cpminvid
  let cA: class A
  let cR: class R
  let cT: class T
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume m2cpminvid.i: |- I = ( N cPolyMatToMat R )
  assume m2cpminvid.a: |- A = ( N Mat R )
  assume m2cpminvid.k: |- K = ( Base ` A )
  assume m2cpminvid.t: |- T = ( N matToPolyMat R )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. K ) -> ( I ` ( T ` M ) ) = M )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cK
    wcel
    #
    w3a
    #
    cM
    cT
    cfv
    #
    cI
    cfv
    #
    vx
    vy
    cN
    cN
    cc0
    vx
    cv
    #
    vy
    cv
    #
    @4
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    vx
    vy
    cN
    cN
    @6
    @7
    cM
    co
    #
    cmpt2
    #
    cM
    @0
    @1
    @2
    @4
    cN
    cR
    ccpmat
    co
    #
    wcel
    @5
    @11
    wceq
    cA
    cK
    cR
    @14
    cT
    cM
    cN
    @14
    eqid
    #
    m2cpminvid.t
    m2cpminvid.a
    m2cpminvid.k
    m2cpm
    vx
    vy
    cR
    @14
    cI
    @4
    cN
    crg
    m2cpminvid.i
    @15
    cpm2mval
    syld3an3
    @3
    vx
    vy
    cN
    cN
    @10
    @12
    @3
    @6
    cN
    wcel
    #
    @7
    cN
    wcel
    #
    w3a
    #
    @10
    cc0
    @12
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cco1
    cfv
    #
    cfv
    #
    @12
    @18
    cc0
    @9
    @22
    @18
    @8
    @21
    cco1
    @3
    @16
    @17
    @8
    @21
    wceq
    cA
    cK
    @19
    cR
    @20
    cT
    cM
    cN
    crg
    @6
    @7
    m2cpminvid.t
    m2cpminvid.a
    m2cpminvid.k
    @19
    eqid
    #
    @20
    eqid
    #
    mat2pmatvalel
    3impb
    fveq2d
    fveq1d
    @18
    @1
    @12
    cR
    cbs
    cfv
    #
    wcel
    @12
    @23
    wceq
    @0
    @1
    @2
    @16
    @17
    simp12
    @18
    cA
    cK
    cR
    @6
    @7
    @26
    cM
    cN
    m2cpminvid.a
    @26
    eqid
    #
    m2cpminvid.k
    @3
    @16
    @17
    simp2
    @3
    @16
    @17
    simp3
    @0
    @1
    @2
    @16
    @17
    simp13
    matecld
    #
    @20
    @19
    cR
    @26
    @12
    @24
    @25
    @27
    ply1sclid
    syl2anc
    eqtr4d
    mpt2eq3dva
    @3
    @13
    cM
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    @13
    co
    @30
    @31
    cM
    co
    #
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @3
    @33
    vi
    vj
    cN
    cN
    @3
    @30
    cN
    wcel
    #
    @31
    cN
    wcel
    #
    wa
    wa
    #
    vx
    vy
    @30
    @31
    cN
    cN
    @12
    @32
    @13
    cvv
    @37
    @13
    eqidd
    @6
    @30
    wceq
    @7
    @31
    wceq
    wa
    @12
    @32
    wceq
    @37
    @6
    @30
    @7
    @31
    cM
    oveq12
    adantl
    @3
    @35
    @36
    simprl
    @3
    @35
    @36
    simprr
    @37
    @30
    @31
    cM
    ovexd
    ovmpt2d
    ralrimivva
    @3
    @13
    cK
    wcel
    @2
    @29
    @34
    wb
    @3
    vx
    vy
    cA
    cK
    @12
    cR
    @26
    cN
    crg
    m2cpminvid.a
    @27
    m2cpminvid.k
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @28
    matbas2d
    @0
    @1
    @2
    simp3
    cA
    cK
    cR
    vi
    vj
    cN
    @13
    cM
    m2cpminvid.a
    m2cpminvid.k
    eqmat
    syl2anc
    mpbird
    3eqtrd
end
