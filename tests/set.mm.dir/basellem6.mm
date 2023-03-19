include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "divcnv.mm"
include "mp1i.mm"
include "c2.mm"
include "cmul.mm"
include "caddc.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "nnrecre.mm"
include "eqeltrd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylan.mm"
include "peano2nnd.mm"
include "nnrecred.mm"
include "cle.mm"
include "nnre.mm"
include "nnred.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0addge1.mm"
include "syl2anc.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "lep1d.mm"
include "letrd.mm"
include "clt.mm"
include "wb.mm"
include "nngt0.mm"
include "nngt0d.mm"
include "lerec.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "3brtr4d.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "climsqz2.mm"
include "trud.mm"

theorem basellem6
  let vn: setvar n
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cH: class H
  let vj: setvar j
  let cM: class M
  let cA: class A
  let cJ: class J
  let cK: class K
  let cN: class N
  assume basel.g: |- G = ( n e. NN |-> ( 1 / ( ( 2 x. n ) + 1 ) ) )


  assert |- G ~~> 0

  proof
    cG
    cc0
    cli
    wbr
    wtru
    cc0
    vk
    vn
    cn
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cG
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    c1
    cc
    wcel
    @2
    cc0
    cli
    wbr
    wtru
    ax-1cn
    c1
    vn
    divcnv
    mp1i
    cG
    cvv
    wcel
    wtru
    cG
    vn
    cn
    c1
    c2
    @0
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    cvv
    basel.g
    vn
    cn
    @5
    nnex
    mptex
    eqeltri
    a1i
    wtru
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    @6
    @2
    cfv
    #
    c1
    @6
    cdiv
    co
    #
    cr
    @7
    @9
    @10
    wceq
    wtru
    vn
    @6
    @1
    @10
    cn
    @2
    @0
    @6
    c1
    cdiv
    oveq2
    @2
    eqid
    c1
    @6
    cdiv
    ovex
    fvmpt
    adantl
    #
    @7
    @10
    cr
    wcel
    wtru
    @6
    nnrecre
    adantl
    eqeltrd
    @8
    @6
    cG
    cfv
    #
    c1
    c2
    @6
    cmul
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cr
    @7
    @12
    @15
    wceq
    wtru
    vn
    @6
    @5
    @15
    cn
    cG
    @0
    @6
    wceq
    #
    @4
    @14
    c1
    cdiv
    @16
    @3
    @13
    c1
    caddc
    @0
    @6
    c2
    cmul
    oveq2
    oveq1d
    oveq2d
    basel.g
    c1
    @14
    cdiv
    ovex
    fvmpt
    adantl
    #
    @8
    @14
    @8
    @13
    wtru
    c2
    cn
    wcel
    #
    @7
    @13
    cn
    wcel
    @18
    wtru
    2nn
    a1i
    c2
    @6
    nnmulcl
    sylan
    #
    peano2nnd
    #
    nnrecred
    eqeltrd
    @8
    @15
    @10
    @12
    @9
    cle
    @8
    @6
    @14
    cle
    wbr
    #
    @15
    @10
    cle
    wbr
    #
    @8
    @6
    @13
    @14
    @7
    @6
    cr
    wcel
    #
    wtru
    @6
    nnre
    adantl
    #
    @8
    @13
    @19
    nnred
    #
    @8
    @14
    @20
    nnred
    #
    @8
    @6
    @6
    @6
    caddc
    co
    #
    @13
    cle
    @8
    @23
    @6
    cn0
    wcel
    #
    @6
    @27
    cle
    wbr
    @24
    @7
    @28
    wtru
    @6
    nnnn0
    adantl
    @6
    @6
    nn0addge1
    syl2anc
    @8
    @6
    @8
    @6
    @24
    recnd
    2timesd
    breqtrrd
    @8
    @13
    @25
    lep1d
    letrd
    @8
    @23
    cc0
    @6
    clt
    wbr
    #
    @14
    cr
    wcel
    cc0
    @14
    clt
    wbr
    @21
    @22
    wb
    @24
    @7
    @29
    wtru
    @6
    nngt0
    adantl
    @26
    @8
    @14
    @20
    nngt0d
    @6
    @14
    lerec
    syl22anc
    mpbid
    @17
    @11
    3brtr4d
    @8
    cc0
    @15
    @12
    cle
    @8
    @15
    @8
    @14
    @8
    @14
    @20
    nnrpd
    rpreccld
    rpge0d
    @17
    breqtrrd
    climsqz2
    trud
end
