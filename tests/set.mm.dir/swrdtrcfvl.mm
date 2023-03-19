include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cfz.mm"
include "wceq.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "a1i.mm"
include "lencl.mm"
include "nn0zd.mm"
include "adantr.mm"
include "simpr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "ige2m1fz1.mm"
include "syl.mm"
include "swrd0fvlsw.mm"
include "syldan.mm"
include "cc.mm"
include "nn0cnd.mm"
include "sub1m1.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem swrdtrcfvl
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ 2 <_ ( # ` W ) ) -> ( lastS ` ( W substr <. 0 , ( ( # ` W ) - 1 ) >. ) ) = ( W ` ( ( # ` W ) - 2 ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    c2
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    cW
    cc0
    @1
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    clsw
    cfv
    #
    @4
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @1
    c2
    cmin
    co
    #
    cW
    cfv
    @0
    @2
    @4
    c1
    @1
    cfz
    co
    wcel
    #
    @5
    @7
    wceq
    @3
    @1
    c2
    cuz
    cfv
    wcel
    #
    @9
    @3
    c2
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @2
    @10
    @11
    @3
    2z
    a1i
    @0
    @12
    @2
    @0
    @1
    cV
    cW
    lencl
    #
    nn0zd
    adantr
    @0
    @2
    simpr
    c2
    @1
    eluz2
    syl3anbrc
    @1
    ige2m1fz1
    syl
    @4
    cV
    cW
    swrd0fvlsw
    syldan
    @3
    @6
    @8
    cW
    @0
    @6
    @8
    wceq
    #
    @2
    @0
    @1
    cc
    wcel
    @14
    @0
    @1
    @13
    nn0cnd
    @1
    sub1m1
    syl
    adantr
    fveq2d
    eqtrd
end
