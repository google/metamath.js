include "cword.mm"
include "wcel.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "c2.mm"
include "wceq.mm"
include "ccatws1cl.mm"
include "ccatws1lenOLD.mm"
include "stoic3.mm"
include "wa.mm"
include "oveq1d.mm"
include "cn0.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cn.mm"
include "add1p1.mm"
include "3syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "3adant3.mm"

theorem ccatw2s1lenOLD
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( W e. Word V /\ X e. V /\ Y e. V ) -> ( # ` ( ( W ++ <" X "> ) ++ <" Y "> ) ) = ( ( # ` W ) + 2 ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    cW
    cX
    cs1
    cconcat
    co
    #
    cY
    cs1
    cconcat
    co
    chash
    cfv
    #
    @4
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cW
    chash
    cfv
    #
    c2
    caddc
    co
    #
    @1
    @2
    @4
    @0
    wcel
    @3
    @5
    @7
    wceq
    cV
    cW
    cX
    ccatws1cl
    cV
    @4
    cY
    ccatws1lenOLD
    stoic3
    @1
    @2
    @7
    @9
    wceq
    @3
    @1
    @2
    wa
    #
    @7
    @8
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    @9
    @10
    @6
    @11
    c1
    caddc
    cV
    cW
    cX
    ccatws1lenOLD
    oveq1d
    @1
    @12
    @9
    wceq
    #
    @2
    @1
    @8
    cn0
    wcel
    @8
    cc
    wcel
    @13
    cV
    cW
    lencl
    @8
    nn0cn
    @8
    add1p1
    3syl
    adantr
    eqtrd
    3adant3
    eqtrd
end
