include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "creps.mm"
include "co.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cword.mm"
include "wceq.mm"
include "cn0.mm"
include "nnnn0.mm"
include "repsw.mm"
include "sylan2.mm"
include "lsw.mm"
include "syl.mm"
include "cc0.mm"
include "cfzo.mm"
include "simpl.mm"
include "adantl.mm"
include "repswlen.mm"
include "oveq1d.mm"
include "fzo0end.mm"
include "eqeltrd.mm"
include "repswsymb.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem repswlsw
  let cS: class S
  let cN: class N
  let cV: class V


  assert |- ( ( S e. V /\ N e. NN ) -> ( lastS ` ( S repeatS N ) ) = S )

  proof
    cS
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cS
    cN
    creps
    co
    #
    clsw
    cfv
    #
    @3
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @3
    cfv
    #
    cS
    @2
    @3
    cV
    cword
    #
    wcel
    #
    @4
    @7
    wceq
    @1
    @0
    cN
    cn0
    wcel
    #
    @9
    cN
    nnnn0
    #
    cS
    cN
    cV
    repsw
    sylan2
    @3
    @8
    lsw
    syl
    @2
    @0
    @10
    @6
    cc0
    cN
    cfzo
    co
    #
    wcel
    @7
    cS
    wceq
    @0
    @1
    simpl
    @1
    @10
    @0
    @11
    adantl
    @2
    @6
    cN
    c1
    cmin
    co
    #
    @12
    @2
    @5
    cN
    c1
    cmin
    @1
    @0
    @10
    @5
    cN
    wceq
    @11
    cS
    cN
    cV
    repswlen
    sylan2
    oveq1d
    @1
    @13
    @12
    wcel
    @0
    cN
    fzo0end
    adantl
    eqeltrd
    cS
    @6
    cN
    cV
    repswsymb
    syl3anc
    eqtrd
end
