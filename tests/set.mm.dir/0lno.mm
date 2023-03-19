include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cba.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cns.mm"
include "co.mm"
include "cpv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "eqid.mm"
include "0oo.mm"
include "cn0v.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprl.mm"
include "nvscl.mm"
include "syl3anc.mm"
include "simprr.mm"
include "nvgcl.mm"
include "0oval.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "nvsz.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "nvzcl.mm"
include "syl.mm"
include "nv0rid.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "ralrimiva.mm"
include "islno.mm"
include "mpbir2and.mm"

theorem 0lno
  let cU: class U
  let cL: class L
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume 0lno.0: |- Z = ( U 0op W )
  assume 0lno.7: |- L = ( U LnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> Z e. L )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    wa
    #
    cZ
    cL
    wcel
    cU
    cba
    cfv
    #
    cW
    cba
    cfv
    #
    cZ
    wf
    vx
    cv
    #
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    #
    vz
    cv
    #
    cU
    cpv
    cfv
    #
    co
    #
    cZ
    cfv
    #
    @5
    @6
    cZ
    cfv
    #
    cW
    cns
    cfv
    #
    co
    #
    @9
    cZ
    cfv
    #
    cW
    cpv
    cfv
    #
    co
    #
    wceq
    #
    vz
    @3
    wral
    vy
    @3
    wral
    #
    vx
    cc
    wral
    cU
    cW
    @3
    @4
    cZ
    @3
    eqid
    #
    @4
    eqid
    #
    0lno.0
    0oo
    @2
    @20
    vx
    cc
    @2
    @5
    cc
    wcel
    #
    wa
    #
    @19
    vy
    vz
    @3
    @3
    @24
    @6
    @3
    wcel
    #
    @9
    @3
    wcel
    #
    wa
    #
    wa
    #
    @12
    cW
    cn0v
    cfv
    #
    @18
    @28
    @0
    @1
    @11
    @3
    wcel
    #
    @12
    @29
    wceq
    @0
    @1
    @23
    @27
    simplll
    #
    @0
    @1
    @23
    @27
    simpllr
    #
    @28
    @0
    @8
    @3
    wcel
    #
    @26
    @30
    @31
    @28
    @0
    @23
    @25
    @33
    @31
    @2
    @23
    @27
    simplr
    #
    @24
    @25
    @26
    simprl
    #
    @5
    @6
    @7
    cU
    @3
    @21
    @7
    eqid
    #
    nvscl
    syl3anc
    @24
    @25
    @26
    simprr
    #
    @8
    @9
    cU
    @10
    @3
    @21
    @10
    eqid
    #
    nvgcl
    syl3anc
    @11
    cU
    cZ
    cW
    @3
    @29
    @21
    @29
    eqid
    #
    0lno.0
    0oval
    syl3anc
    @28
    @18
    @5
    @29
    @14
    co
    #
    @29
    @17
    co
    @29
    @29
    @17
    co
    #
    @29
    @28
    @15
    @40
    @16
    @29
    @17
    @28
    @13
    @29
    @5
    @14
    @28
    @0
    @1
    @25
    @13
    @29
    wceq
    @31
    @32
    @35
    @6
    cU
    cZ
    cW
    @3
    @29
    @21
    @39
    0lno.0
    0oval
    syl3anc
    oveq2d
    @28
    @0
    @1
    @26
    @16
    @29
    wceq
    @31
    @32
    @37
    @9
    cU
    cZ
    cW
    @3
    @29
    @21
    @39
    0lno.0
    0oval
    syl3anc
    oveq12d
    @28
    @40
    @29
    @29
    @17
    @28
    @1
    @23
    @40
    @29
    wceq
    @32
    @34
    @5
    @14
    cW
    @29
    @14
    eqid
    #
    @39
    nvsz
    syl2anc
    oveq1d
    @28
    @1
    @29
    @4
    wcel
    #
    @41
    @29
    wceq
    @32
    @28
    @1
    @43
    @32
    cW
    @4
    @29
    @22
    @39
    nvzcl
    syl
    @29
    cW
    @17
    @4
    @29
    @22
    @17
    eqid
    #
    @39
    nv0rid
    syl2anc
    3eqtrd
    eqtr4d
    ralrimivva
    ralrimiva
    vx
    vy
    vz
    @7
    @14
    cZ
    cU
    @10
    @17
    cL
    cW
    @3
    @4
    @21
    @22
    @38
    @44
    @36
    @42
    0lno.7
    islno
    mpbir2and
end
