include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf.mm"
include "cc0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cbs.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "w3a.mm"
include "cpl1.mm"
include "cn0.mm"
include "cmat.mm"
include "simp2.mm"
include "simp3.mm"
include "cpmatpmat.mm"
include "3expa.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "0nn0.mm"
include "coe1fvalcl.mm"
include "sylancl.mm"
include "matbas2d.mm"
include "fmptd.mm"
include "cpm2mfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem cpm2mf
  let cA: class A
  let cR: class R
  let cS: class S
  let cI: class I
  let cK: class K
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume cpm2mf.a: |- A = ( N Mat R )
  assume cpm2mf.k: |- K = ( Base ` A )
  assume cpm2mf.s: |- S = ( N ConstPolyMat R )
  assume cpm2mf.i: |- I = ( N cPolyMatToMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> I : S --> K )

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
    cS
    cK
    cI
    wf
    cS
    cK
    vm
    cS
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
    wf
    @2
    vm
    cS
    @9
    cK
    @10
    @2
    @5
    cS
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cK
    @8
    cR
    cR
    cbs
    cfv
    #
    cN
    crg
    cpm2mf.a
    @13
    eqid
    #
    cpm2mf.k
    @0
    @1
    @11
    simpll
    @0
    @1
    @11
    simplr
    @12
    @3
    cN
    wcel
    #
    @4
    cN
    wcel
    #
    w3a
    #
    @6
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
    @8
    @13
    wcel
    @17
    cN
    @18
    cmat
    co
    #
    @20
    cbs
    cfv
    #
    @18
    @3
    @4
    @19
    @5
    cN
    @20
    eqid
    #
    @19
    eqid
    #
    @21
    eqid
    #
    @12
    @15
    @16
    simp2
    @12
    @15
    @16
    simp3
    @12
    @15
    @5
    @21
    wcel
    #
    @16
    @0
    @1
    @11
    @25
    @21
    @20
    @18
    cR
    cS
    @5
    cN
    crg
    cpm2mf.s
    @18
    eqid
    #
    @22
    @24
    cpmatpmat
    3expa
    3ad2ant1
    matecld
    0nn0
    @7
    @19
    @18
    cR
    @6
    @13
    cc0
    @7
    eqid
    @23
    @26
    @14
    coe1fvalcl
    sylancl
    matbas2d
    @10
    eqid
    fmptd
    @2
    cS
    cK
    cI
    @10
    vx
    vy
    cR
    cS
    vm
    cI
    cN
    crg
    cpm2mf.i
    cpm2mf.s
    cpm2mfval
    feq1d
    mpbird
end
