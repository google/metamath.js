include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "cr.mm"
include "wceq.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "sumex.mm"
include "fvmpt.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn.mm"
include "adantl.mm"
include "c2.mm"
include "cfa.mm"
include "cneg.mm"
include "cexp.mm"
include "weq.mm"
include "fveq2.mm"
include "negeqd.mm"
include "oveq2d.mm"
include "ovex.mm"
include "crp.mm"
include "cz.mm"
include "2rp.mm"
include "cn0.mm"
include "nnnn0.mm"
include "faccl.mm"
include "syl.mm"
include "nnzd.mm"
include "znegcld.mm"
include "rpexpcl.mm"
include "sylancr.mm"
include "rpred.mm"
include "eqeltrd.mm"
include "fsumrecl.mm"

theorem aaliou3lem5
  let cA: class A
  let cF: class F
  let cH: class H
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume aaliou3lem.c: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )
  assume aaliou3lem.d: |- L = sum_ b e. NN ( F ` b )
  assume aaliou3lem.e: |- H = ( c e. NN |-> sum_ b e. ( 1 ... c ) ( F ` b ) )

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint F b
  disjoint F c
  disjoint L c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a d
  disjoint a e
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint F d
  disjoint F e
  disjoint L d
  disjoint L e
  disjoint L f
  disjoint c f
  disjoint d f
  disjoint e f
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint A d
  disjoint A e
  assert |- ( A e. NN -> ( H ` A ) e. RR )

  proof
    cA
    cn
    wcel
    #
    cA
    cH
    cfv
    c1
    cA
    cfz
    co
    #
    vb
    cv
    #
    cF
    cfv
    #
    vb
    csu
    #
    cr
    vc
    cA
    c1
    vc
    cv
    #
    cfz
    co
    #
    @3
    vb
    csu
    @4
    cn
    cH
    @5
    cA
    wceq
    @6
    @1
    @3
    vb
    @5
    cA
    c1
    cfz
    oveq2
    sumeq1d
    aaliou3lem.e
    @1
    @3
    vb
    sumex
    fvmpt
    @0
    @1
    @3
    vb
    @0
    c1
    cA
    fzfid
    @0
    @2
    @1
    wcel
    #
    wa
    @2
    cn
    wcel
    #
    @3
    cr
    wcel
    @7
    @8
    @0
    @2
    cA
    elfznn
    adantl
    @8
    @3
    c2
    @2
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cr
    va
    @2
    c2
    va
    cv
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    @11
    cn
    cF
    va
    vb
    weq
    #
    @14
    @10
    c2
    cexp
    @15
    @13
    @9
    @12
    @2
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.c
    c2
    @10
    cexp
    ovex
    fvmpt
    @8
    @11
    @8
    c2
    crp
    wcel
    @10
    cz
    wcel
    @11
    crp
    wcel
    2rp
    @8
    @9
    @8
    @9
    @8
    @2
    cn0
    wcel
    @9
    cn
    wcel
    @2
    nnnn0
    @2
    faccl
    syl
    nnzd
    znegcld
    c2
    @10
    rpexpcl
    sylancr
    rpred
    eqeltrd
    syl
    fsumrecl
    eqeltrd
end
