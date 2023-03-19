include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "wceq.mm"
include "simpl.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "adantl.mm"
include "simpr.mm"
include "lencl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantr.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "swrdid.mm"
include "eqtrd.mm"

theorem wrdcctswrd
  let cM: class M
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( ( W substr <. 0 , M >. ) ++ ( W substr <. M , ( # ` W ) >. ) ) = W )

  proof
    cW
    cV
    cword
    wcel
    #
    cM
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cW
    cc0
    cM
    cop
    csubstr
    co
    cW
    cM
    @1
    cop
    csubstr
    co
    cconcat
    co
    #
    cW
    cc0
    @1
    cop
    csubstr
    co
    #
    cW
    @4
    @0
    cc0
    cc0
    cM
    cfz
    co
    wcel
    #
    @3
    @1
    @2
    wcel
    #
    @5
    @6
    wceq
    @0
    @3
    simpl
    @3
    @7
    @0
    @3
    cM
    cn0
    wcel
    @7
    cM
    @1
    elfznn0
    cM
    0elfz
    syl
    adantl
    @0
    @3
    simpr
    @0
    @8
    @3
    @0
    @1
    cn0
    wcel
    @8
    cV
    cW
    lencl
    @1
    nn0fz0
    sylib
    adantr
    cV
    cW
    cc0
    cM
    @1
    ccatswrd
    syl13anc
    @0
    @6
    cW
    wceq
    @3
    cV
    cW
    swrdid
    adantr
    eqtrd
end
