include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "w3o.mm"
include "cxnn0.mm"
include "hashxnn0.mm"
include "xnn0le2is012.mm"
include "sylan.mm"
include "ex.mm"
include "hasheq0.mm"
include "eqneqall.mm"
include "syl6bi.mm"
include "com12.mm"
include "csn.mm"
include "hash1snb.mm"
include "vex.mm"
include "weq.mm"
include "preq12.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "spc2ev.mm"
include "exlimiv.mm"
include "imp.mm"
include "a1d.mm"
include "expcom.mm"
include "hash2pr.mm"
include "3jaoi.mm"
include "syld.mm"
include "com23.mm"
include "fveq2.mm"
include "cfn.mm"
include "hashprlei.mm"
include "simpri.mm"
include "syl6eqbr.mm"
include "exlimivv.mm"
include "impbid1.mm"

theorem hashle2pr
  let cP: class P
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint P a
  disjoint P b
  disjoint a b
  disjoint P c
  disjoint a c
  disjoint b c
  assert |- ( ( P e. V /\ P =/= (/) ) -> ( ( # ` P ) <_ 2 <-> E. a E. b P = { a , b } ) )

  proof
    cP
    cV
    wcel
    #
    cP
    c0
    wne
    #
    wa
    cP
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    cP
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    wex
    va
    wex
    #
    @0
    @1
    @3
    @8
    wi
    @0
    @3
    @1
    @8
    @0
    @3
    @2
    cc0
    wceq
    #
    @2
    c1
    wceq
    #
    @2
    c2
    wceq
    #
    w3o
    #
    @1
    @8
    wi
    #
    @0
    @3
    @12
    @0
    @2
    cxnn0
    wcel
    @3
    @12
    cP
    cV
    hashxnn0
    @2
    xnn0le2is012
    sylan
    ex
    @12
    @0
    @13
    @9
    @0
    @13
    wi
    @10
    @11
    @0
    @9
    @13
    @0
    @9
    cP
    c0
    wceq
    @13
    cP
    cV
    hasheq0
    @8
    cP
    c0
    eqneqall
    syl6bi
    com12
    @0
    @10
    @13
    @0
    @10
    wa
    @8
    @1
    @0
    @10
    @8
    @0
    @10
    cP
    vc
    cv
    #
    csn
    #
    wceq
    #
    vc
    wex
    @8
    cP
    cV
    vc
    hash1snb
    @16
    @8
    vc
    @7
    @16
    va
    vb
    @14
    @14
    vc
    vex
    #
    @17
    va
    vc
    weq
    vb
    vc
    weq
    wa
    #
    @6
    @15
    cP
    @18
    @6
    @14
    @14
    cpr
    @15
    @4
    @5
    @14
    @14
    preq12
    @14
    dfsn2
    syl6eqr
    eqeq2d
    spc2ev
    exlimiv
    syl6bi
    imp
    a1d
    expcom
    @0
    @11
    @13
    @0
    @11
    wa
    @8
    @1
    cP
    cV
    va
    vb
    hash2pr
    a1d
    expcom
    3jaoi
    com12
    syld
    com23
    imp
    @7
    @3
    va
    vb
    @7
    @2
    @6
    chash
    cfv
    #
    c2
    cle
    cP
    @6
    chash
    fveq2
    @6
    cfn
    wcel
    @19
    c2
    cle
    wbr
    @4
    @5
    hashprlei
    simpri
    syl6eqbr
    exlimivv
    impbid1
end
