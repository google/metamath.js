include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cn.mm"
include "c3.mm"
include "cle.mm"
include "wbr.mm"
include "csn.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cfz.mm"
include "1nn.mm"
include "cop.mm"
include "wf.mm"
include "cz.mm"
include "1zzd.mm"
include "id.mm"
include "fsnd.mm"
include "prmex.mm"
include "snex.mm"
include "elmap.mm"
include "sylibr.mm"
include "cr.mm"
include "1re.mm"
include "simpl.mm"
include "fvsng.mm"
include "sylancr.mm"
include "sumeq2dv.mm"
include "cc.mm"
include "prmz.mm"
include "zcnd.mm"
include "eqidd.mm"
include "sumsn.mm"
include "eqtr2d.mm"
include "1le3.mm"
include "jctil.mm"
include "elsni.mm"
include "adantl.mm"
include "fveq12d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "1z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "breq1.mm"
include "sumeq1d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"

theorem nnsum3primesprm
  let cP: class P
  let vf: setvar f
  let vk: setvar k
  let vd: setvar d
  let vx: setvar x

  disjoint P d
  disjoint P f
  disjoint P k
  disjoint d f
  disjoint d k
  disjoint f k
  disjoint k x
  assert |- ( P e. Prime -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 3 /\ P = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    cP
    cprime
    wcel
    #
    c1
    cn
    wcel
    c1
    c3
    cle
    wbr
    #
    cP
    c1
    csn
    #
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @2
    cmap
    co
    #
    wrex
    #
    vd
    cv
    #
    c3
    cle
    wbr
    #
    cP
    c1
    @11
    cfz
    co
    #
    @5
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @13
    cmap
    co
    #
    wrex
    #
    vd
    cn
    wrex
    1nn
    @0
    c1
    cP
    cop
    csn
    #
    @9
    wcel
    #
    @1
    cP
    @2
    c1
    @19
    cfv
    #
    vk
    csu
    #
    wceq
    #
    wa
    #
    @10
    @0
    @2
    cprime
    @19
    wf
    @20
    @0
    c1
    cP
    cz
    cprime
    @0
    1zzd
    @0
    id
    fsnd
    cprime
    @2
    @19
    prmex
    c1
    snex
    elmap
    sylibr
    @0
    @23
    @1
    @0
    @22
    @2
    cP
    vk
    csu
    #
    cP
    @0
    @2
    @21
    cP
    vk
    @0
    @3
    @2
    wcel
    #
    wa
    c1
    cr
    wcel
    #
    @0
    @21
    cP
    wceq
    1re
    @0
    @26
    simpl
    c1
    cP
    cr
    cprime
    fvsng
    sylancr
    sumeq2dv
    @0
    @27
    cP
    cc
    wcel
    @25
    cP
    wceq
    1re
    @0
    cP
    cP
    prmz
    zcnd
    cP
    cP
    vk
    c1
    cr
    @3
    c1
    wceq
    #
    cP
    eqidd
    sumsn
    sylancr
    eqtr2d
    1le3
    jctil
    @8
    @24
    vf
    @19
    @9
    @4
    @19
    wceq
    #
    @7
    @23
    @1
    @29
    @6
    @22
    cP
    @29
    @2
    @5
    @21
    vk
    @29
    @26
    wa
    @3
    c1
    @4
    @19
    @29
    @26
    simpl
    @26
    @28
    @29
    @3
    c1
    elsni
    adantl
    fveq12d
    sumeq2dv
    eqeq2d
    anbi2d
    rspcev
    syl2anc
    @18
    @10
    vd
    c1
    cn
    @11
    c1
    wceq
    #
    @16
    @8
    vf
    @17
    @9
    @30
    @13
    @2
    cprime
    cmap
    @30
    @13
    c1
    c1
    cfz
    co
    #
    @2
    @11
    c1
    c1
    cfz
    oveq2
    c1
    cz
    wcel
    @31
    @2
    wceq
    1z
    c1
    fzsn
    ax-mp
    syl6eq
    #
    oveq2d
    @30
    @12
    @1
    @15
    @7
    @11
    c1
    c3
    cle
    breq1
    @30
    @14
    @6
    cP
    @30
    @13
    @2
    @5
    vk
    @32
    sumeq1d
    eqeq2d
    anbi12d
    rexeqbidv
    rspcev
    sylancr
end
