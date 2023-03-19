include "cn.mm"
include "wcel.mm"
include "czn.mm"
include "cfv.mm"
include "cur.mm"
include "csn.mm"
include "chash.mm"
include "csu.mm"
include "c0g.mm"
include "cphi.mm"
include "cbs.mm"
include "cv.mm"
include "cc0.mm"
include "cif.mm"
include "eqid.mm"
include "znfi.mm"
include "dchrfi.mm"
include "wa.mm"
include "cc.mm"
include "simprr.mm"
include "dchrf.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "fsumcom.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "sumdchr2.mm"
include "wb.mm"
include "velsn.mm"
include "ifbi.mm"
include "mp1i.mm"
include "eqtr4d.mm"
include "sumeq2dv.mm"
include "dchrsum.mm"
include "3eqtr3d.mm"
include "wss.mm"
include "wral.mm"
include "cuz.mm"
include "cfn.mm"
include "wo.mm"
include "cn0.mm"
include "ccrg.mm"
include "crg.mm"
include "nnnn0.mm"
include "zncrng.mm"
include "crngring.mm"
include "ringidcl.mm"
include "4syl.mm"
include "snssd.mm"
include "hashcl.mm"
include "nn0cn.mm"
include "3syl.mm"
include "ralrimivw.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "cabl.mm"
include "cgrp.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "phicl.mm"
include "nncnd.mm"
include "3eqtr4d.mm"
include "eqidd.mm"
include "sumsn.mm"
include "syl2anc.mm"

theorem dchrhash
  let cD: class D
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.1: class .1.
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let wph: wff ph
  let cZ: class Z
  assume sumdchr.g: |- G = ( DChr ` N )
  assume sumdchr.d: |- D = ( Base ` G )


  assert |- ( N e. NN -> ( # ` D ) = ( phi ` N ) )

  proof
    cN
    cn
    wcel
    #
    cN
    czn
    cfv
    #
    cur
    cfv
    #
    csn
    #
    cD
    chash
    cfv
    #
    va
    csu
    #
    cG
    c0g
    cfv
    #
    csn
    #
    cN
    cphi
    cfv
    #
    vx
    csu
    #
    @4
    @8
    @0
    @1
    cbs
    cfv
    #
    va
    cv
    #
    @3
    wcel
    #
    @4
    cc0
    cif
    #
    va
    csu
    #
    cD
    vx
    cv
    #
    @7
    wcel
    #
    @8
    cc0
    cif
    #
    vx
    csu
    #
    @5
    @9
    @0
    @10
    cD
    @11
    @15
    cfv
    #
    vx
    csu
    #
    va
    csu
    cD
    @10
    @19
    va
    csu
    #
    vx
    csu
    @14
    @18
    @0
    @10
    cD
    @19
    va
    vx
    @10
    cN
    @1
    @1
    eqid
    #
    @10
    eqid
    #
    znfi
    #
    cD
    cG
    cN
    sumdchr.g
    sumdchr.d
    dchrfi
    #
    @0
    @11
    @10
    wcel
    #
    @15
    cD
    wcel
    #
    wa
    wa
    #
    @10
    cc
    @11
    @15
    @28
    @10
    cD
    cG
    cN
    @15
    @1
    sumdchr.g
    @22
    sumdchr.d
    @23
    @0
    @26
    @27
    simprr
    dchrf
    @0
    @26
    @27
    simprl
    ffvelrnd
    fsumcom
    @0
    @10
    @20
    @13
    va
    @0
    @26
    wa
    #
    @20
    @11
    @2
    wceq
    #
    @4
    cc0
    cif
    #
    @13
    @29
    vx
    @11
    @10
    cD
    @2
    cG
    cN
    @1
    sumdchr.g
    sumdchr.d
    @22
    @2
    eqid
    #
    @23
    @0
    @26
    simpl
    @0
    @26
    simpr
    sumdchr2
    @12
    @30
    wb
    @13
    @31
    wceq
    @29
    va
    @2
    velsn
    @12
    @30
    @4
    cc0
    ifbi
    mp1i
    eqtr4d
    sumeq2dv
    @0
    cD
    @21
    @17
    vx
    @0
    @27
    wa
    #
    @21
    @15
    @6
    wceq
    #
    @8
    cc0
    cif
    #
    @17
    @33
    @10
    cD
    @6
    cG
    cN
    @15
    @1
    va
    sumdchr.g
    @22
    sumdchr.d
    @6
    eqid
    #
    @0
    @27
    simpr
    @23
    dchrsum
    @16
    @34
    wb
    @17
    @35
    wceq
    @33
    vx
    @6
    velsn
    @16
    @34
    @8
    cc0
    ifbi
    mp1i
    eqtr4d
    sumeq2dv
    3eqtr3d
    @0
    @3
    @10
    wss
    @4
    cc
    wcel
    #
    va
    @3
    wral
    @10
    cc0
    cuz
    cfv
    #
    wss
    #
    @10
    cfn
    wcel
    #
    wo
    @5
    @14
    wceq
    @0
    @2
    @10
    @0
    cN
    cn0
    wcel
    @1
    ccrg
    wcel
    @1
    crg
    wcel
    @2
    @10
    wcel
    #
    cN
    nnnn0
    cN
    @1
    @22
    zncrng
    @1
    crngring
    @10
    @1
    @2
    @23
    @32
    ringidcl
    4syl
    #
    snssd
    @0
    @37
    va
    @3
    @0
    cD
    cfn
    wcel
    #
    @4
    cn0
    wcel
    @37
    @25
    cD
    hashcl
    @4
    nn0cn
    3syl
    #
    ralrimivw
    @0
    @40
    @39
    @24
    olcd
    @3
    @10
    @4
    va
    cc0
    sumss2
    syl21anc
    @0
    @7
    cD
    wss
    @8
    cc
    wcel
    #
    vx
    @7
    wral
    cD
    @38
    wss
    #
    @43
    wo
    @9
    @18
    wceq
    @0
    @6
    cD
    @0
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    @6
    cD
    wcel
    #
    cG
    cN
    sumdchr.g
    dchrabl
    cG
    ablgrp
    cD
    cG
    @6
    sumdchr.d
    @36
    grpidcl
    3syl
    #
    snssd
    @0
    @45
    vx
    @7
    @0
    @8
    cN
    phicl
    nncnd
    #
    ralrimivw
    @0
    @43
    @46
    @25
    olcd
    @7
    cD
    @8
    vx
    cc0
    sumss2
    syl21anc
    3eqtr4d
    @0
    @41
    @37
    @5
    @4
    wceq
    @42
    @44
    @4
    @4
    va
    @2
    @10
    @30
    @4
    eqidd
    sumsn
    syl2anc
    @0
    @47
    @45
    @9
    @8
    wceq
    @48
    @49
    @8
    @8
    vx
    @6
    cD
    @34
    @8
    eqidd
    sumsn
    syl2anc
    3eqtr3d
end
