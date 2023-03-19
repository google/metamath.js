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
include "cfzo.mm"
include "cres.mm"
include "cconcat.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "swrdcl.mm"
include "adantr.mm"
include "simpl.mm"
include "cuz.mm"
include "simpr.mm"
include "elfzuz.mm"
include "eluzfz1.mm"
include "3syl.mm"
include "elfzuz2.mm"
include "eluzfz2.mm"
include "ccatswrd.mm"
include "syl13anc.mm"
include "swrd0val.mm"
include "oveq1d.mm"
include "swrdid.mm"
include "3eqtr3rd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem wrdsplex
  let vv: setvar v
  let cS: class S
  let cN: class N
  let cW: class W

  disjoint N v
  disjoint S v
  disjoint W v
  assert |- ( ( W e. Word S /\ N e. ( 0 ... ( # ` W ) ) ) -> E. v e. Word S W = ( ( W |` ( 0 ..^ N ) ) ++ v ) )

  proof
    cW
    cS
    cword
    #
    wcel
    #
    cN
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
    cN
    @2
    cop
    csubstr
    co
    #
    @0
    wcel
    #
    cW
    cW
    cc0
    cN
    cfzo
    co
    cres
    #
    @6
    cconcat
    co
    #
    wceq
    #
    cW
    @8
    vv
    cv
    #
    cconcat
    co
    #
    wceq
    #
    vv
    @0
    wrex
    @1
    @7
    @4
    cS
    cW
    cN
    @2
    swrdcl
    adantr
    @5
    cW
    cc0
    cN
    cop
    csubstr
    co
    #
    @6
    cconcat
    co
    #
    cW
    cc0
    @2
    cop
    csubstr
    co
    #
    @9
    cW
    @5
    @1
    cc0
    cc0
    cN
    cfz
    co
    wcel
    #
    @4
    @2
    @3
    wcel
    #
    @15
    @16
    wceq
    @1
    @4
    simpl
    @5
    @4
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @17
    @1
    @4
    simpr
    #
    cN
    cc0
    @2
    elfzuz
    cc0
    cN
    eluzfz1
    3syl
    @20
    @5
    @4
    @2
    @19
    wcel
    @18
    @20
    cN
    cc0
    @2
    elfzuz2
    cc0
    @2
    eluzfz2
    3syl
    cS
    cW
    cc0
    cN
    @2
    ccatswrd
    syl13anc
    @5
    @14
    @8
    @6
    cconcat
    cS
    cW
    cN
    swrd0val
    oveq1d
    @1
    @16
    cW
    wceq
    @4
    cS
    cW
    swrdid
    adantr
    3eqtr3rd
    @13
    @10
    vv
    @6
    @0
    @11
    @6
    wceq
    @12
    @9
    cW
    @11
    @6
    @8
    cconcat
    oveq2
    eqeq2d
    rspcev
    syl2anc
end
