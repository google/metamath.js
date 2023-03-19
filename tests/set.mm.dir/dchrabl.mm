include "cn.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqidd.mm"
include "czn.mm"
include "cv.mm"
include "cui.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "w3a.mm"
include "eqid.mm"
include "simp2.mm"
include "simp3.mm"
include "dchrmulcl.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "cc.mm"
include "cvv.mm"
include "fvexd.mm"
include "wf.mm"
include "dchrf.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "wceq.mm"
include "mulass.mm"
include "adantl.mm"
include "caofass.mm"
include "simpr1.mm"
include "simpr2.mm"
include "dchrmul.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "id.mm"
include "dchr1cl.mm"
include "simpr.mm"
include "dchrmulid2.mm"
include "dchrinvcl.mm"
include "simpld.mm"
include "simprd.mm"
include "isgrpd.mm"
include "mulcom.mm"
include "caofcom.mm"
include "isabld.mm"

theorem dchrabl
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume dchrabl.g: |- G = ( DChr ` N )


  assert |- ( N e. NN -> G e. Abel )

  proof
    cN
    cn
    wcel
    #
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    cG
    @0
    @1
    eqidd
    #
    @0
    @2
    eqidd
    #
    @0
    vx
    vy
    vz
    @1
    @2
    cG
    vk
    cN
    czn
    cfv
    #
    cbs
    cfv
    #
    vk
    cv
    #
    @5
    cui
    cfv
    #
    wcel
    #
    c1
    @7
    vx
    cv
    #
    cfv
    cdiv
    co
    cc0
    cif
    cmpt
    #
    vk
    @6
    @9
    c1
    cc0
    cif
    cmpt
    #
    @3
    @4
    @0
    @10
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    w3a
    #
    @1
    @2
    cG
    cN
    @10
    @14
    @5
    dchrabl.g
    @5
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    @0
    @13
    @15
    simp2
    #
    @0
    @13
    @15
    simp3
    #
    dchrmulcl
    #
    @0
    @13
    @15
    vz
    cv
    #
    @1
    wcel
    #
    w3a
    wa
    #
    @10
    @14
    @2
    co
    #
    @23
    cmul
    cof
    #
    co
    #
    @10
    @14
    @23
    @2
    co
    #
    @27
    co
    #
    @26
    @23
    @2
    co
    @10
    @29
    @2
    co
    @25
    @10
    @14
    @27
    co
    #
    @23
    @27
    co
    @10
    @14
    @23
    @27
    co
    #
    @27
    co
    @28
    @30
    @25
    va
    vb
    vc
    @6
    cmul
    cmul
    cc
    cmul
    @10
    @14
    @23
    cmul
    cvv
    @25
    @5
    cbs
    fvexd
    @0
    @13
    @15
    @6
    cc
    @10
    wf
    @24
    @16
    @6
    @1
    cG
    cN
    @10
    @5
    dchrabl.g
    @17
    @18
    @6
    eqid
    #
    @20
    dchrf
    #
    3adant3r3
    @0
    @13
    @15
    @6
    cc
    @14
    wf
    @24
    @16
    @6
    @1
    cG
    cN
    @14
    @5
    dchrabl.g
    @17
    @18
    @33
    @21
    dchrf
    #
    3adant3r3
    @25
    @6
    @1
    cG
    cN
    @23
    @5
    dchrabl.g
    @17
    @18
    @33
    @0
    @13
    @15
    @24
    simpr3
    #
    dchrf
    va
    cv
    #
    cc
    wcel
    #
    vb
    cv
    #
    cc
    wcel
    #
    vc
    cv
    #
    cc
    wcel
    w3a
    @37
    @39
    cmul
    co
    #
    @41
    cmul
    co
    @37
    @39
    @41
    cmul
    co
    cmul
    co
    wceq
    @25
    @37
    @39
    @41
    mulass
    adantl
    caofass
    @25
    @26
    @31
    @23
    @27
    @25
    @1
    @2
    cG
    cN
    @10
    @14
    @5
    dchrabl.g
    @17
    @18
    @19
    @0
    @13
    @15
    @24
    simpr1
    #
    @0
    @13
    @15
    @24
    simpr2
    #
    dchrmul
    oveq1d
    @25
    @29
    @32
    @10
    @27
    @25
    @1
    @2
    cG
    cN
    @14
    @23
    @5
    dchrabl.g
    @17
    @18
    @19
    @44
    @36
    dchrmul
    oveq2d
    3eqtr4d
    @25
    @1
    @2
    cG
    cN
    @26
    @23
    @5
    dchrabl.g
    @17
    @18
    @19
    @0
    @13
    @15
    @26
    @1
    wcel
    @24
    @22
    3adant3r3
    @36
    dchrmul
    @25
    @1
    @2
    cG
    cN
    @10
    @29
    @5
    dchrabl.g
    @17
    @18
    @19
    @43
    @25
    @1
    @2
    cG
    cN
    @14
    @23
    @5
    dchrabl.g
    @17
    @18
    @19
    @44
    @36
    dchrmulcl
    dchrmul
    3eqtr4d
    @0
    @6
    @1
    @8
    @12
    vk
    cG
    cN
    @5
    dchrabl.g
    @17
    @18
    @33
    @8
    eqid
    #
    @12
    eqid
    #
    @0
    id
    dchr1cl
    @0
    @13
    wa
    #
    @6
    @1
    @2
    @8
    @12
    vk
    cG
    cN
    @10
    @5
    dchrabl.g
    @17
    @18
    @33
    @45
    @46
    @19
    @0
    @13
    simpr
    #
    dchrmulid2
    @47
    @11
    @1
    wcel
    #
    @11
    @10
    @2
    co
    @12
    wceq
    #
    @47
    @6
    @1
    @2
    @8
    @12
    vk
    cG
    @11
    cN
    @10
    @5
    dchrabl.g
    @17
    @18
    @33
    @45
    @46
    @19
    @48
    @11
    eqid
    dchrinvcl
    #
    simpld
    @47
    @49
    @50
    @51
    simprd
    isgrpd
    @16
    @31
    @14
    @10
    @27
    co
    @26
    @14
    @10
    @2
    co
    @16
    va
    vb
    @6
    cmul
    cc
    @10
    @14
    cvv
    @16
    @5
    cbs
    fvexd
    @34
    @35
    @38
    @40
    wa
    @42
    @39
    @37
    cmul
    co
    wceq
    @16
    @37
    @39
    mulcom
    adantl
    caofcom
    @16
    @1
    @2
    cG
    cN
    @10
    @14
    @5
    dchrabl.g
    @17
    @18
    @19
    @20
    @21
    dchrmul
    @16
    @1
    @2
    cG
    cN
    @14
    @10
    @5
    dchrabl.g
    @17
    @18
    @19
    @21
    @20
    dchrmul
    3eqtr4d
    isabld
end
