include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cn.mm"
include "csquarenn.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "eluzelz.mm"
include "zsqcl.mm"
include "syl.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "sq1.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "1red.mm"
include "eluzelre.mm"
include "cle.mm"
include "0le1.mm"
include "a1i.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "lt2sqd.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "resqcld.mm"
include "posdifd.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "csqrt.mm"
include "cq.mm"
include "wa.mm"
include "cc.mm"
include "rmspecsqrtnq.mm"
include "eldifbd.mm"
include "intnand.mm"
include "cv.mm"
include "crab.mm"
include "df-squarenn.mm"
include "eleq2i.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "bitr2i.mm"
include "sylnib.mm"
include "eldifd.mm"

theorem rmspecnonsq
  let cA: class A
  let va: setvar a


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( ( A ^ 2 ) - 1 ) e. ( NN \ []NN ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cA
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    cn
    csquarenn
    @0
    @2
    cz
    wcel
    cc0
    @2
    clt
    wbr
    #
    @2
    cn
    wcel
    #
    @0
    @1
    c1
    @0
    cA
    cz
    wcel
    @1
    cz
    wcel
    c2
    cA
    eluzelz
    cA
    zsqcl
    syl
    @0
    1zzd
    zsubcld
    @0
    c1
    @1
    clt
    wbr
    @3
    @0
    c1
    c1
    c2
    cexp
    co
    #
    @1
    clt
    sq1
    @0
    c1
    cA
    clt
    wbr
    #
    @5
    @1
    clt
    wbr
    @0
    cA
    cn
    wcel
    @6
    cA
    eluz2b2
    simprbi
    @0
    c1
    cA
    @0
    1red
    #
    c2
    cA
    eluzelre
    #
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    @0
    cA
    cA
    eluzge2nn0
    nn0ge0d
    lt2sqd
    mpbid
    syl5eqbrr
    @0
    c1
    @1
    @7
    @0
    cA
    @8
    resqcld
    posdifd
    mpbid
    @2
    elnnz
    sylanbrc
    @0
    @4
    @2
    csqrt
    cfv
    #
    cq
    wcel
    #
    wa
    #
    @2
    csquarenn
    wcel
    #
    @0
    @10
    @4
    @0
    @9
    cc
    cq
    cA
    rmspecsqrtnq
    eldifbd
    intnand
    @12
    @2
    va
    cv
    #
    csqrt
    cfv
    #
    cq
    wcel
    #
    va
    cn
    crab
    #
    wcel
    @11
    csquarenn
    @16
    @2
    va
    df-squarenn
    eleq2i
    @15
    @10
    va
    @2
    cn
    @13
    @2
    wceq
    @14
    @9
    cq
    @13
    @2
    csqrt
    fveq2
    eleq1d
    elrab
    bitr2i
    sylnib
    eldifd
end
