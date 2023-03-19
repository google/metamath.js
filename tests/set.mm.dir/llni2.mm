include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "eqidd.mm"
include "neeq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simpl1.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "adantr.mm"
include "islln3.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem llni2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let vr: setvar r
  let vs: setvar s
  assume llni2.j: |- .\/ = ( join ` K )
  assume llni2.a: |- A = ( Atoms ` K )
  assume llni2.n: |- N = ( LLines ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ P =/= Q ) -> ( P .\/ Q ) e. N )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    wa
    #
    cP
    cQ
    c.or
    co
    #
    cN
    wcel
    #
    vr
    cv
    #
    vs
    cv
    #
    wne
    #
    @6
    @8
    @9
    c.or
    co
    #
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    @5
    @1
    @2
    @4
    @6
    @6
    wceq
    #
    @14
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    simpl3
    @3
    @4
    simpr
    @5
    @6
    eqidd
    @13
    @4
    @15
    wa
    cP
    @9
    wne
    #
    @6
    cP
    @9
    c.or
    co
    #
    wceq
    #
    wa
    vr
    vs
    cP
    cQ
    cA
    cA
    @8
    cP
    wceq
    #
    @10
    @16
    @12
    @18
    @8
    cP
    @9
    neeq1
    @19
    @11
    @17
    @6
    @8
    cP
    @9
    c.or
    oveq1
    eqeq2d
    anbi12d
    @9
    cQ
    wceq
    #
    @16
    @4
    @18
    @15
    @9
    cQ
    cP
    neeq2
    @20
    @17
    @6
    @6
    @9
    cQ
    cP
    c.or
    oveq2
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    @5
    @0
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @14
    wb
    @0
    @1
    @2
    @4
    simpl1
    @3
    @22
    @4
    cA
    @21
    c.or
    cK
    cP
    cQ
    @21
    eqid
    #
    llni2.j
    llni2.a
    hlatjcl
    adantr
    cA
    @21
    c.or
    cK
    cN
    @6
    vs
    vr
    @23
    llni2.j
    llni2.a
    llni2.n
    islln3
    syl2anc
    mpbird
end
