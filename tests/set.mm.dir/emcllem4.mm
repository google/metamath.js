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
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "nnrecre.mm"
include "eqeltrd.mm"
include "crp.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "1rp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpaddcl.mm"
include "sylancr.mm"
include "rpred.mm"
include "clt.mm"
include "1re.mm"
include "ltaddrp.mm"
include "rplogcld.mm"
include "cle.mm"
include "relogcld.mm"
include "ce.mm"
include "efgt1p.mm"
include "syl.mm"
include "wb.mm"
include "rpefcld.mm"
include "logltb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "relogefd.mm"
include "breqtrd.mm"
include "ltled.mm"
include "3brtr4d.mm"
include "rpge0d.mm"
include "climsqz2.mm"
include "trud.mm"

theorem emcllem4
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cN: class N
  let cT: class T
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )
  assume emcl.3: |- H = ( n e. NN |-> ( log ` ( 1 + ( 1 / n ) ) ) )

  disjoint H m
  disjoint m n
  disjoint i k
  disjoint i x
  disjoint F i
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G i
  disjoint G k
  disjoint G x
  disjoint k m
  disjoint H k
  disjoint N m
  disjoint N n
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint T m
  disjoint n x
  disjoint T n
  disjoint T x
  assert |- H ~~> 0

  proof
    cH
    cc0
    cli
    wbr
    wtru
    cc0
    vm
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
    cH
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
    cH
    cvv
    wcel
    wtru
    cH
    vn
    cn
    c1
    @1
    caddc
    co
    #
    clog
    cfv
    #
    cmpt
    cvv
    emcl.3
    vn
    cn
    @4
    nnex
    mptex
    eqeltri
    a1i
    wtru
    vm
    cv
    #
    cn
    wcel
    #
    wa
    #
    @5
    @2
    cfv
    #
    c1
    @5
    cdiv
    co
    #
    cr
    @6
    @8
    @9
    wceq
    wtru
    vn
    @5
    @1
    @9
    cn
    @2
    @0
    @5
    c1
    cdiv
    oveq2
    #
    @2
    eqid
    c1
    @5
    cdiv
    ovex
    fvmpt
    adantl
    #
    @6
    @9
    cr
    wcel
    wtru
    @5
    nnrecre
    adantl
    #
    eqeltrd
    @7
    @5
    cH
    cfv
    #
    @7
    @13
    c1
    @9
    caddc
    co
    #
    clog
    cfv
    #
    crp
    @6
    @13
    @15
    wceq
    wtru
    vn
    @5
    @4
    @15
    cn
    cH
    @0
    @5
    wceq
    #
    @3
    @14
    clog
    @16
    @1
    @9
    c1
    caddc
    @10
    oveq2d
    fveq2d
    emcl.3
    @14
    clog
    fvex
    fvmpt
    adantl
    #
    @7
    @14
    @7
    @14
    @7
    c1
    crp
    wcel
    @9
    crp
    wcel
    #
    @14
    crp
    wcel
    #
    1rp
    @7
    @5
    @6
    @5
    crp
    wcel
    wtru
    @5
    nnrp
    adantl
    rpreccld
    #
    c1
    @9
    rpaddcl
    sylancr
    #
    rpred
    @7
    c1
    cr
    wcel
    @18
    c1
    @14
    clt
    wbr
    1re
    @20
    c1
    @9
    ltaddrp
    sylancr
    rplogcld
    eqeltrd
    #
    rpred
    @7
    @15
    @9
    @13
    @8
    cle
    @7
    @15
    @9
    @7
    @14
    @21
    relogcld
    @12
    @7
    @15
    @9
    ce
    cfv
    #
    clog
    cfv
    #
    @9
    clt
    @7
    @14
    @23
    clt
    wbr
    #
    @15
    @24
    clt
    wbr
    #
    @7
    @18
    @25
    @20
    @9
    efgt1p
    syl
    @7
    @19
    @23
    crp
    wcel
    @25
    @26
    wb
    @21
    @7
    @9
    @12
    rpefcld
    @14
    @23
    logltb
    syl2anc
    mpbid
    @7
    @9
    @12
    relogefd
    breqtrd
    ltled
    @17
    @11
    3brtr4d
    @7
    @13
    @22
    rpge0d
    climsqz2
    trud
end
