include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cs2.mm"
include "cv.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "1le2.mm"
include "breq2.mm"
include "mpbiri.mm"
include "wrdsymb1.mm"
include "sylan2.mm"
include "clsw.mm"
include "cmin.mm"
include "co.mm"
include "lsw.mm"
include "oveq1.mm"
include "2m1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "sylan9eq.mm"
include "cn.mm"
include "2nn.mm"
include "lswlgt0cl.mm"
include "mpan.mm"
include "eqeltrrd.mm"
include "wrdlen2s2.mm"
include "id.mm"
include "eqidd.mm"
include "s2eqd.mm"
include "eqeq2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"

theorem wrdl2exs2
  let vt: setvar t
  let cS: class S
  let cW: class W
  let vs: setvar s

  disjoint S s
  disjoint S t
  disjoint s t
  disjoint W s
  disjoint W t
  assert |- ( ( W e. Word S /\ ( # ` W ) = 2 ) -> E. s e. S E. t e. S W = <" s t "> )

  proof
    cW
    cS
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cc0
    cW
    cfv
    #
    cS
    wcel
    #
    c1
    cW
    cfv
    #
    cS
    wcel
    cW
    @5
    @7
    cs2
    #
    wceq
    #
    cW
    vs
    cv
    #
    vt
    cv
    #
    cs2
    #
    wceq
    #
    vt
    cS
    wrex
    vs
    cS
    wrex
    @3
    @1
    c1
    @2
    cle
    wbr
    #
    @6
    @3
    @14
    c1
    c2
    cle
    wbr
    1le2
    @2
    c2
    c1
    cle
    breq2
    mpbiri
    cS
    cW
    wrdsymb1
    sylan2
    @4
    cW
    clsw
    cfv
    #
    @7
    cS
    @1
    @3
    @15
    @2
    c1
    cmin
    co
    #
    cW
    cfv
    @7
    cW
    @0
    lsw
    @3
    @16
    c1
    cW
    @3
    @16
    c2
    c1
    cmin
    co
    c1
    @2
    c2
    c1
    cmin
    oveq1
    2m1e1
    syl6eq
    fveq2d
    sylan9eq
    c2
    cn
    wcel
    @4
    @15
    cS
    wcel
    2nn
    c2
    cS
    cW
    lswlgt0cl
    mpan
    eqeltrrd
    cS
    cW
    wrdlen2s2
    @13
    @9
    cW
    @5
    @11
    cs2
    #
    wceq
    vs
    vt
    @5
    @7
    cS
    cS
    @10
    @5
    wceq
    #
    @12
    @17
    cW
    @18
    @10
    @11
    @5
    @11
    @18
    id
    @18
    @11
    eqidd
    s2eqd
    eqeq2d
    @11
    @7
    wceq
    #
    @17
    @8
    cW
    @19
    @5
    @11
    @5
    @7
    @19
    @5
    eqidd
    @19
    id
    s2eqd
    eqeq2d
    rspc2ev
    syl3anc
end
