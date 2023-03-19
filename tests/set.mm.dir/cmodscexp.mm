include "cclm.mm"
include "wcel.mm"
include "ci.mm"
include "wa.mm"
include "cn.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmg.mm"
include "co.mm"
include "cexp.mm"
include "cc.mm"
include "cn0.mm"
include "wceq.mm"
include "ax-icn.mm"
include "a1i.mm"
include "nnnn0.mm"
include "cnfldexp.mm"
include "syl2an.mm"
include "csubmnd.mm"
include "csubrg.mm"
include "clmsubrg.mm"
include "eqid.mm"
include "subrgsubm.mm"
include "syl.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "simplr.mm"
include "submmulgcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"

theorem cmodscexp
  let cF: class F
  let cK: class K
  let cN: class N
  let cW: class W
  assume cmodscexp.f: |- F = ( Scalar ` W )
  assume cmodscexp.k: |- K = ( Base ` F )


  assert |- ( ( ( W e. CMod /\ _i e. K ) /\ N e. NN ) -> ( _i ^ N ) e. K )

  proof
    cW
    cclm
    wcel
    #
    ci
    cK
    wcel
    #
    wa
    #
    cN
    cn
    wcel
    #
    wa
    #
    cN
    ci
    ccnfld
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    ci
    cN
    cexp
    co
    #
    cK
    @2
    ci
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    @7
    @8
    wceq
    @3
    @9
    @2
    ax-icn
    a1i
    cN
    nnnn0
    #
    ci
    cN
    cnfldexp
    syl2an
    @4
    cK
    @5
    csubmnd
    cfv
    wcel
    #
    @10
    @1
    @7
    cK
    wcel
    @0
    @12
    @1
    @3
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @12
    cF
    cK
    cW
    cmodscexp.f
    cmodscexp.k
    clmsubrg
    cK
    ccnfld
    @5
    @5
    eqid
    subrgsubm
    syl
    ad2antrr
    @3
    @10
    @2
    @11
    adantl
    @0
    @1
    @3
    simplr
    cK
    @6
    @5
    cN
    ci
    @6
    eqid
    submmulgcl
    syl3anc
    eqeltrrd
end
