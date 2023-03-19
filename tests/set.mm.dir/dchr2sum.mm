include "cv.mm"
include "csg.mm"
include "cfv.mm"
include "co.mm"
include "csu.mm"
include "c0g.mm"
include "wceq.mm"
include "cphi.mm"
include "cc0.mm"
include "cif.mm"
include "ccj.mm"
include "cmul.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "cn.mm"
include "cabl.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "3syl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "dchrsum.mm"
include "wa.mm"
include "cminusg.mm"
include "cof.mm"
include "cplusg.mm"
include "adantr.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "grpinvcl.mm"
include "dchrmul.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "cvv.mm"
include "cc.mm"
include "wf.mm"
include "dchrf.mm"
include "ffn.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simpr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "ccom.mm"
include "dchrinv.mm"
include "fvco3.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "sumeq2dv.mm"
include "wb.mm"
include "grpsubeq0.mm"
include "ifbid.mm"
include "3eqtr3d.mm"

theorem dchr2sum
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  assume dchr2sum.g: |- G = ( DChr ` N )
  assume dchr2sum.z: |- Z = ( Z/nZ ` N )
  assume dchr2sum.d: |- D = ( Base ` G )
  assume dchr2sum.b: |- B = ( Base ` Z )
  assume dchr2sum.x: |- ( ph -> X e. D )
  assume dchr2sum.y: |- ( ph -> Y e. D )

  disjoint B a
  disjoint G a
  disjoint a ph
  disjoint X a
  disjoint Y a
  disjoint Z a
  assert |- ( ph -> sum_ a e. B ( ( X ` a ) x. ( * ` ( Y ` a ) ) ) = if ( X = Y , ( phi ` N ) , 0 ) )

  proof
    wph
    cB
    va
    cv
    #
    cX
    cY
    cG
    csg
    cfv
    #
    co
    #
    cfv
    #
    va
    csu
    @2
    cG
    c0g
    cfv
    #
    wceq
    #
    cN
    cphi
    cfv
    #
    cc0
    cif
    cB
    @0
    cX
    cfv
    #
    @0
    cY
    cfv
    ccj
    cfv
    #
    cmul
    co
    #
    va
    csu
    cX
    cY
    wceq
    #
    @6
    cc0
    cif
    wph
    cB
    cD
    @4
    cG
    cN
    @2
    cZ
    va
    dchr2sum.g
    dchr2sum.z
    dchr2sum.d
    @4
    eqid
    #
    wph
    cG
    cgrp
    wcel
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    @2
    cD
    wcel
    wph
    cN
    cn
    wcel
    #
    cG
    cabl
    wcel
    #
    @12
    wph
    @13
    @15
    dchr2sum.x
    cD
    cG
    cN
    cX
    dchr2sum.g
    dchr2sum.d
    dchrrcl
    syl
    #
    cG
    cN
    dchr2sum.g
    dchrabl
    #
    cG
    ablgrp
    #
    3syl
    #
    dchr2sum.x
    dchr2sum.y
    cD
    cG
    @1
    cX
    cY
    dchr2sum.d
    @1
    eqid
    #
    grpsubcl
    syl3anc
    dchr2sum.b
    dchrsum
    wph
    cB
    @3
    @9
    va
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @3
    @0
    cX
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    cmul
    cof
    co
    #
    cfv
    #
    @7
    @0
    @25
    cfv
    #
    cmul
    co
    #
    @9
    @23
    @0
    @2
    @26
    @23
    @2
    cX
    @25
    cG
    cplusg
    cfv
    #
    co
    #
    @26
    @23
    @13
    @14
    @2
    @31
    wceq
    wph
    @13
    @22
    dchr2sum.x
    adantr
    #
    wph
    @14
    @22
    dchr2sum.y
    adantr
    #
    cD
    @30
    cG
    @24
    @1
    cX
    cY
    dchr2sum.d
    @30
    eqid
    #
    @24
    eqid
    #
    @21
    grpsubval
    syl2anc
    @23
    cD
    @30
    cG
    cN
    cX
    @25
    cZ
    dchr2sum.g
    dchr2sum.z
    dchr2sum.d
    @34
    @32
    @23
    @12
    @14
    @25
    cD
    wcel
    @23
    @15
    @16
    @12
    wph
    @15
    @22
    @17
    adantr
    @18
    @19
    3syl
    @33
    cD
    cG
    @24
    cY
    dchr2sum.d
    @35
    grpinvcl
    syl2anc
    #
    dchrmul
    eqtrd
    fveq1d
    @23
    cX
    cB
    wfn
    #
    @25
    cB
    wfn
    #
    cB
    cvv
    wcel
    #
    @22
    @27
    @29
    wceq
    @23
    cB
    cc
    cX
    wf
    @37
    @23
    cB
    cD
    cG
    cN
    cX
    cZ
    dchr2sum.g
    dchr2sum.z
    dchr2sum.d
    dchr2sum.b
    @32
    dchrf
    cB
    cc
    cX
    ffn
    syl
    @23
    cB
    cc
    @25
    wf
    @38
    @23
    cB
    cD
    cG
    cN
    @25
    cZ
    dchr2sum.g
    dchr2sum.z
    dchr2sum.d
    dchr2sum.b
    @36
    dchrf
    cB
    cc
    @25
    ffn
    syl
    @39
    @23
    cB
    cZ
    cbs
    cfv
    cvv
    dchr2sum.b
    cZ
    cbs
    fvex
    eqeltri
    a1i
    wph
    @22
    simpr
    #
    cB
    cmul
    cX
    @25
    cvv
    @0
    fnfvof
    syl22anc
    @23
    @28
    @8
    @7
    cmul
    @23
    @28
    @0
    ccj
    cY
    ccom
    #
    cfv
    #
    @8
    @23
    @0
    @25
    @41
    @23
    cD
    cG
    @24
    cN
    cY
    dchr2sum.g
    dchr2sum.d
    @33
    @35
    dchrinv
    fveq1d
    @23
    cB
    cc
    cY
    wf
    @22
    @42
    @8
    wceq
    @23
    cB
    cD
    cG
    cN
    cY
    cZ
    dchr2sum.g
    dchr2sum.z
    dchr2sum.d
    dchr2sum.b
    @33
    dchrf
    @40
    cB
    cc
    @0
    ccj
    cY
    fvco3
    syl2anc
    eqtrd
    oveq2d
    3eqtrd
    sumeq2dv
    wph
    @5
    @10
    @6
    cc0
    wph
    @12
    @13
    @14
    @5
    @10
    wb
    @20
    dchr2sum.x
    dchr2sum.y
    cD
    cG
    @1
    cX
    cY
    @4
    dchr2sum.d
    @11
    @21
    grpsubeq0
    syl3anc
    ifbid
    3eqtr3d
end
