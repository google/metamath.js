include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cpfx.mm"
include "clsw.mm"
include "cs1.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "swrdlsw.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "cc0.mm"
include "cfz.mm"
include "wceq.mm"
include "cfn.mm"
include "wrdfin.mm"
include "1elfz0hash.mm"
include "sylan.mm"
include "fznn0sub2.mm"
include "syl.mm"
include "pfxcctswrd.mm"
include "syldan.mm"
include "eqtrd.mm"

theorem pfxlswccat
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( ( W prefix ( ( # ` W ) - 1 ) ) ++ <" ( lastS ` W ) "> ) = W )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    cW
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cpfx
    co
    #
    cW
    clsw
    cfv
    cs1
    #
    cconcat
    co
    @5
    cW
    @4
    @3
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cW
    @2
    @6
    @7
    @5
    cconcat
    @2
    @7
    @6
    cV
    cW
    swrdlsw
    eqcomd
    oveq2d
    @0
    @1
    @4
    cc0
    @3
    cfz
    co
    #
    wcel
    #
    @8
    cW
    wceq
    @2
    c1
    @9
    wcel
    #
    @10
    @0
    cW
    cfn
    wcel
    @1
    @11
    cV
    cW
    wrdfin
    cW
    1elfz0hash
    sylan
    c1
    @3
    fznn0sub2
    syl
    @4
    cV
    cW
    pfxcctswrd
    syldan
    eqtrd
end
