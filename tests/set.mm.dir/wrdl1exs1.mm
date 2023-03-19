include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cs1.mm"
include "cv.mm"
include "wrex.mm"
include "eqs1.mm"
include "cle.mm"
include "wbr.mm"
include "1le1.mm"
include "breq2.mm"
include "mpbiri.mm"
include "wrdsymb1.mm"
include "sylan2.mm"
include "s1eq.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "rspcedv.mm"
include "mpd.mm"

theorem wrdl1exs1
  let cS: class S
  let cW: class W
  let vs: setvar s

  disjoint S s
  disjoint W s
  assert |- ( ( W e. Word S /\ ( # ` W ) = 1 ) -> E. s e. S W = <" s "> )

  proof
    cW
    cS
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
    #
    cW
    cc0
    cW
    cfv
    #
    cs1
    #
    wceq
    #
    cW
    vs
    cv
    #
    cs1
    #
    wceq
    #
    vs
    cS
    wrex
    cS
    cW
    eqs1
    @3
    @9
    @6
    vs
    @4
    cS
    @2
    @0
    c1
    @1
    cle
    wbr
    #
    @4
    cS
    wcel
    @2
    @10
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
    cS
    cW
    wrdsymb1
    sylan2
    @3
    @7
    @4
    wceq
    #
    wa
    @8
    @5
    cW
    @11
    @8
    @5
    wceq
    @3
    @7
    @4
    s1eq
    adantl
    eqeq2d
    rspcedv
    mpd
end
