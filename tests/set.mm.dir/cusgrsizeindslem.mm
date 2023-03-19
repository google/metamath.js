include "ccusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "crab.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "ccplgr.mm"
include "cusgrcplgr.mm"
include "nbcplgr.mm"
include "sylan.mm"
include "3adant2.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "wex.mm"
include "cusgr.mm"
include "wa.mm"
include "cusgrusgr.mm"
include "anim1i.mm"
include "nbusgrf1o.mm"
include "syl.mm"
include "wb.mm"
include "cpr.mm"
include "nbusgr.mm"
include "adantr.mm"
include "rabfi.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "3adant3.mm"
include "cfusgr.mm"
include "isfusgr.mm"
include "sylibr.mm"
include "cedg.mm"
include "fusgrfis.mm"
include "syl5eqel.mm"
include "hasheqf1o.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "hashdifsn.mm"
include "3adant1.mm"
include "3eqtr3d.mm"

theorem cusgrsizeindslem
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vn: setvar n
  assume cusgrsizeindb0.v: |- V = ( Vtx ` G )
  assume cusgrsizeindb0.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint E f
  disjoint E n
  disjoint e f
  disjoint e n
  disjoint f n
  disjoint G f
  disjoint G n
  disjoint N f
  disjoint N n
  disjoint V f
  disjoint V n
  assert |- ( ( G e. ComplUSGraph /\ V e. Fin /\ N e. V ) -> ( # ` { e e. E | N e. e } ) = ( ( # ` V ) - 1 ) )

  proof
    cG
    ccusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cN
    cV
    wcel
    #
    w3a
    #
    cG
    cN
    cnbgr
    co
    #
    chash
    cfv
    #
    cV
    cN
    csn
    cdif
    #
    chash
    cfv
    #
    cN
    ve
    cv
    wcel
    #
    ve
    cE
    crab
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    c1
    cmin
    co
    #
    @3
    @4
    @6
    chash
    @0
    @2
    @4
    @6
    wceq
    #
    @1
    @0
    cG
    ccplgr
    wcel
    @2
    @12
    cG
    cusgrcplgr
    cG
    cN
    cV
    cusgrsizeindb0.v
    nbcplgr
    sylan
    3adant2
    fveq2d
    @3
    @5
    @10
    wceq
    #
    @4
    @9
    vf
    cv
    wf1o
    vf
    wex
    #
    @3
    cG
    cusgr
    wcel
    #
    @2
    wa
    #
    @14
    @0
    @2
    @16
    @1
    @0
    @15
    @2
    cG
    cusgrusgr
    #
    anim1i
    3adant2
    cN
    ve
    vf
    cE
    cG
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    nbusgrf1o
    syl
    @3
    @4
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    @13
    @14
    wb
    @0
    @1
    @18
    @2
    @0
    @1
    wa
    #
    @4
    cN
    vn
    cv
    cpr
    cE
    wcel
    #
    vn
    cV
    crab
    #
    cfn
    @0
    @4
    @22
    wceq
    #
    @1
    @0
    @15
    @23
    @17
    vn
    cE
    cG
    cN
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    nbusgr
    syl
    adantr
    @1
    @22
    cfn
    wcel
    @0
    @21
    vn
    cV
    rabfi
    adantl
    eqeltrd
    3adant3
    @0
    @1
    @19
    @2
    @20
    cG
    cfusgr
    wcel
    #
    @19
    @20
    @15
    @1
    wa
    @24
    @0
    @15
    @1
    @17
    anim1i
    cG
    cV
    cusgrsizeindb0.v
    isfusgr
    sylibr
    @24
    cE
    cfn
    wcel
    @19
    @24
    cE
    cG
    cedg
    cfv
    cfn
    cusgrsizeindb0.e
    cG
    fusgrfis
    syl5eqel
    @8
    ve
    cE
    rabfi
    syl
    syl
    3adant3
    @4
    @9
    vf
    hasheqf1o
    syl2anc
    mpbird
    @1
    @2
    @7
    @11
    wceq
    @0
    cV
    cN
    hashdifsn
    3adant1
    3eqtr3d
end
