include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cneg.mm"
include "cexp.mm"
include "cz.mm"
include "wrex.mm"
include "wb.mm"
include "nnz.mm"
include "odd2np1.mm"
include "syl.mm"
include "biimpa.mm"
include "3adant1.mm"
include "wa.mm"
include "simpl1.mm"
include "cmin.mm"
include "cn0.mm"
include "simprr.mm"
include "simpl2.mm"
include "nncnd.mm"
include "1cnd.mm"
include "2z.mm"
include "simprl.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "zcnd.mm"
include "subadd2d.mm"
include "mpbird.mm"
include "nnm1nn0.mm"
include "eqeltrrd.mm"
include "expcld.mm"
include "mulneg2d.mm"
include "sqneg.mm"
include "oveq1d.mm"
include "negcld.mm"
include "cc0.mm"
include "cle.mm"
include "cr.mm"
include "clt.mm"
include "2re.mm"
include "a1i.mm"
include "zred.mm"
include "2pos.mm"
include "nn0ge0d.mm"
include "prodge0.mm"
include "syl22anc.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "2nn0.mm"
include "expmuld.mm"
include "3eqtr4d.mm"
include "expp1d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "negeqd.mm"
include "rexlimddv.mm"

theorem oexpneg
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ N e. NN /\ -. 2 || N ) -> ( -u A ^ N ) = -u ( A ^ N ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    w3a
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    cA
    cneg
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cneg
    #
    wceq
    vn
    cz
    @1
    @2
    @7
    vn
    cz
    wrex
    #
    @0
    @1
    @2
    @12
    @1
    cN
    cz
    wcel
    @2
    @12
    wb
    cN
    nnz
    vn
    cN
    odd2np1
    syl
    biimpa
    3adant1
    @3
    @4
    cz
    wcel
    #
    @7
    wa
    #
    wa
    #
    cA
    @5
    cexp
    co
    #
    cA
    cmul
    co
    #
    cneg
    #
    @9
    @11
    @15
    @16
    @8
    cmul
    co
    #
    @18
    @9
    @15
    @16
    cA
    @15
    cA
    @5
    @0
    @1
    @2
    @14
    simpl1
    #
    @15
    cN
    c1
    cmin
    co
    #
    @5
    cn0
    @15
    @21
    @5
    wceq
    @7
    @3
    @13
    @7
    simprr
    #
    @15
    cN
    c1
    @5
    @15
    cN
    @0
    @1
    @2
    @14
    simpl2
    #
    nncnd
    @15
    1cnd
    @15
    @5
    @15
    c2
    cz
    wcel
    @13
    @5
    cz
    wcel
    2z
    @3
    @13
    @7
    simprl
    #
    c2
    @4
    zmulcl
    sylancr
    zcnd
    subadd2d
    mpbird
    @15
    @1
    @21
    cn0
    wcel
    @23
    cN
    nnm1nn0
    syl
    eqeltrrd
    #
    expcld
    @20
    mulneg2d
    @15
    @8
    @5
    cexp
    co
    #
    @8
    cmul
    co
    #
    @19
    @9
    @15
    @26
    @16
    @8
    cmul
    @15
    @8
    c2
    cexp
    co
    #
    @4
    cexp
    co
    cA
    c2
    cexp
    co
    #
    @4
    cexp
    co
    @26
    @16
    @15
    @28
    @29
    @4
    cexp
    @15
    @0
    @28
    @29
    wceq
    @20
    cA
    sqneg
    syl
    oveq1d
    @15
    @8
    c2
    @4
    @15
    cA
    @20
    negcld
    #
    @15
    @13
    cc0
    @4
    cle
    wbr
    #
    @4
    cn0
    wcel
    @24
    @15
    c2
    cr
    wcel
    #
    @4
    cr
    wcel
    cc0
    c2
    clt
    wbr
    #
    cc0
    @5
    cle
    wbr
    @31
    @32
    @15
    2re
    a1i
    @15
    @4
    @24
    zred
    @33
    @15
    2pos
    a1i
    @15
    @5
    @25
    nn0ge0d
    c2
    @4
    prodge0
    syl22anc
    @4
    elnn0z
    sylanbrc
    #
    c2
    cn0
    wcel
    @15
    2nn0
    a1i
    #
    expmuld
    @15
    cA
    c2
    @4
    @20
    @34
    @35
    expmuld
    3eqtr4d
    oveq1d
    @15
    @8
    @6
    cexp
    co
    @27
    @9
    @15
    @8
    @5
    @30
    @25
    expp1d
    @15
    @6
    cN
    @8
    cexp
    @22
    oveq2d
    eqtr3d
    eqtr3d
    eqtr3d
    @15
    @17
    @10
    @15
    cA
    @6
    cexp
    co
    @17
    @10
    @15
    cA
    @5
    @20
    @25
    expp1d
    @15
    @6
    cN
    cA
    cexp
    @22
    oveq2d
    eqtr3d
    negeqd
    eqtr3d
    rexlimddv
end
