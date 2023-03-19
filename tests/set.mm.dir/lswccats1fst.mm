include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "clsw.mm"
include "wceq.mm"
include "wrdsymb1.mm"
include "lswccats1.mm"
include "syldan.mm"
include "cfzo.mm"
include "simpl.mm"
include "s1cld.mm"
include "cn.mm"
include "cn0.mm"
include "lencl.mm"
include "elnnnn0c.mm"
include "biimpri.mm"
include "sylan.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "eqtr4d.mm"

theorem lswccats1fst
  let cP: class P
  let cV: class V


  assert |- ( ( P e. Word V /\ 1 <_ ( # ` P ) ) -> ( lastS ` ( P ++ <" ( P ` 0 ) "> ) ) = ( ( P ++ <" ( P ` 0 ) "> ) ` 0 ) )

  proof
    cP
    cV
    cword
    #
    wcel
    #
    c1
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    cP
    cc0
    cP
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    clsw
    cfv
    #
    @5
    cc0
    @7
    cfv
    #
    @1
    @3
    @5
    cV
    wcel
    @8
    @5
    wceq
    cV
    cP
    wrdsymb1
    #
    @5
    cV
    cP
    lswccats1
    syldan
    @4
    @1
    @6
    @0
    wcel
    cc0
    cc0
    @2
    cfzo
    co
    wcel
    #
    @9
    @5
    wceq
    @1
    @3
    simpl
    @4
    @5
    cV
    @10
    s1cld
    @4
    @2
    cn
    wcel
    #
    @11
    @1
    @2
    cn0
    wcel
    #
    @3
    @12
    cV
    cP
    lencl
    @12
    @13
    @3
    wa
    @2
    elnnnn0c
    biimpri
    sylan
    @2
    lbfzo0
    sylibr
    cV
    cP
    @6
    cc0
    ccatval1
    syl3anc
    eqtr4d
end
