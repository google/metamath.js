include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "1le1.mm"
include "breq2.mm"
include "mpbiri.mm"
include "wrdsymb1.mm"
include "sylan2.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"

theorem wrdlen1
  let vv: setvar v
  let cV: class V
  let cW: class W

  disjoint V v
  disjoint W v
  assert |- ( ( W e. Word V /\ ( # ` W ) = 1 ) -> E. v e. V ( W ` 0 ) = v )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    cc0
    cW
    cfv
    #
    cV
    wcel
    #
    @3
    vv
    cv
    #
    wceq
    #
    vv
    cV
    wrex
    #
    @2
    @0
    c1
    @1
    cle
    wbr
    #
    @4
    @2
    @8
    c1
    c1
    cle
    wbr
    1le1
    @1
    c1
    c1
    cle
    breq2
    mpbiri
    cV
    cW
    wrdsymb1
    sylan2
    @4
    @5
    @3
    wceq
    #
    vv
    cV
    wrex
    @7
    vv
    @3
    cV
    risset
    @9
    @6
    vv
    cV
    @5
    @3
    eqcom
    rexbii
    bitri
    sylib
end
