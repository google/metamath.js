include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cr.mm"
include "nn0re.mm"
include "adantl.mm"
include "peano2re.mm"
include "syl.mm"
include "eluzelre.mm"
include "reexpcl.mm"
include "sylan.mm"
include "ltp1d.mm"
include "cmin.mm"
include "cmul.mm"
include "cn.mm"
include "uz2m1nn.mm"
include "adantr.mm"
include "nnred.mm"
include "remulcld.mm"
include "1red.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "nnge1d.mm"
include "lemulge12d.mm"
include "leadd1dd.mm"
include "simpr.mm"
include "eluzge2nn0.mm"
include "bernneq2.mm"
include "syl3anc.mm"
include "letrd.mm"
include "ltletrd.mm"

theorem bernneq3
  let cP: class P
  let cN: class N


  assert |- ( ( P e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> N < ( P ^ N ) )

  proof
    cP
    c2
    cuz
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cN
    c1
    caddc
    co
    #
    cP
    cN
    cexp
    co
    #
    @1
    cN
    cr
    wcel
    #
    @0
    cN
    nn0re
    adantl
    #
    @2
    @5
    @3
    cr
    wcel
    @6
    cN
    peano2re
    syl
    #
    @0
    cP
    cr
    wcel
    #
    @1
    @4
    cr
    wcel
    c2
    cP
    eluzelre
    #
    cP
    cN
    reexpcl
    sylan
    #
    @2
    cN
    @6
    ltp1d
    @2
    @3
    cP
    c1
    cmin
    co
    #
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    @4
    @7
    @2
    @12
    cr
    wcel
    @13
    cr
    wcel
    @2
    @11
    cN
    @2
    @11
    @0
    @11
    cn
    wcel
    @1
    cP
    uz2m1nn
    adantr
    #
    nnred
    #
    @6
    remulcld
    #
    @12
    peano2re
    syl
    @10
    @2
    cN
    @12
    c1
    @6
    @16
    @2
    1red
    @2
    cN
    @11
    @6
    @15
    @1
    cc0
    cN
    cle
    wbr
    @0
    cN
    nn0ge0
    adantl
    @2
    @11
    @14
    nnge1d
    lemulge12d
    leadd1dd
    @2
    @8
    @1
    cc0
    cP
    cle
    wbr
    #
    @13
    @4
    cle
    wbr
    @0
    @8
    @1
    @9
    adantr
    @0
    @1
    simpr
    @0
    @17
    @1
    @0
    cP
    cn0
    wcel
    @17
    cP
    eluzge2nn0
    cP
    nn0ge0
    syl
    adantr
    cP
    cN
    bernneq2
    syl3anc
    letrd
    ltletrd
end
