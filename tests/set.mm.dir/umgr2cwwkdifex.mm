include "cumgr.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cclwwlkn.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cfzo.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "eluz2b2.mm"
include "cn0.mm"
include "1nn0.mm"
include "a1i.mm"
include "simpl.mm"
include "simpr.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "sylbi.mm"
include "3ad2ant2.mm"
include "wceq.mm"
include "fveq2.mm"
include "adantl.mm"
include "neeq1d.mm"
include "umgr2cwwk2dif.mm"
include "rspcedvd.mm"

theorem umgr2cwwkdifex
  let vi: setvar i
  let cG: class G
  let cN: class N
  let cW: class W

  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( ( G e. UMGraph /\ N e. ( ZZ>= ` 2 ) /\ W e. ( N ClWWalksN G ) ) -> E. i e. ( 0 ..^ N ) ( W ` i ) =/= ( W ` 0 ) )

  proof
    cG
    cumgr
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    w3a
    #
    vi
    cv
    #
    cW
    cfv
    #
    cc0
    cW
    cfv
    #
    wne
    c1
    cW
    cfv
    #
    @6
    wne
    vi
    c1
    cc0
    cN
    cfzo
    co
    #
    @1
    @0
    c1
    @8
    wcel
    #
    @2
    @1
    cN
    cn
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    wa
    #
    @9
    cN
    eluz2b2
    @12
    c1
    cn0
    wcel
    #
    @10
    @11
    @9
    @13
    @12
    1nn0
    a1i
    @10
    @11
    simpl
    @10
    @11
    simpr
    c1
    cN
    elfzo0
    syl3anbrc
    sylbi
    3ad2ant2
    @3
    @4
    c1
    wceq
    #
    wa
    @5
    @7
    @6
    @14
    @5
    @7
    wceq
    @3
    @4
    c1
    cW
    fveq2
    adantl
    neeq1d
    cG
    cN
    cW
    umgr2cwwk2dif
    rspcedvd
end
