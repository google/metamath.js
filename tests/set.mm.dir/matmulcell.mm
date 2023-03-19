include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cotp.mm"
include "cmmul.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "wi.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "eqid.mm"
include "matmulr.mm"
include "syl6reqr.mm"
include "a1d.mm"
include "syl.mm"
include "adantr.mm"
include "impcom.mm"
include "3adant3.mm"
include "oveqd.mm"
include "cbs.mm"
include "simp1.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2i.mm"
include "adantl.mm"
include "simp3l.mm"
include "simp3r.mm"
include "mamufv.mm"
include "eqtrd.mm"

theorem matmulcell
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let cY: class Y
  assume matmulcell.a: |- A = ( N Mat R )
  assume matmulcell.b: |- B = ( Base ` A )
  assume matmulcell.t: |- .x. = ( .r ` R )
  assume matmulcell.m: |- .X. = ( .r ` A )

  disjoint B j
  disjoint I j
  disjoint J j
  disjoint N j
  disjoint R j
  disjoint X j
  disjoint Y j
  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. B ) /\ ( I e. N /\ J e. N ) ) -> ( I ( X .X. Y ) J ) = ( R gsum ( j e. N |-> ( ( I X j ) ( .r ` R ) ( j Y J ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    wa
    #
    w3a
    #
    cI
    cJ
    cX
    cY
    c.xp
    co
    #
    co
    cI
    cJ
    cX
    cY
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    #
    co
    cR
    vj
    cN
    cI
    vj
    cv
    #
    cX
    co
    @11
    cJ
    cY
    co
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    @7
    @8
    @10
    cI
    cJ
    @7
    c.xp
    @9
    cX
    cY
    @0
    @3
    c.xp
    @9
    wceq
    #
    @6
    @3
    @0
    @13
    @1
    @0
    @13
    wi
    #
    @2
    @1
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    @14
    cA
    cB
    cR
    cN
    cX
    matmulcell.a
    matmulcell.b
    matrcl
    #
    @17
    @13
    @0
    @17
    @9
    cA
    cmulr
    cfv
    c.xp
    cA
    cR
    @9
    cN
    cvv
    matmulcell.a
    @9
    eqid
    #
    matmulr
    matmulcell.m
    syl6reqr
    a1d
    syl
    adantr
    impcom
    3adant3
    oveqd
    oveqd
    @7
    cR
    cbs
    cfv
    #
    cN
    cR
    @12
    vj
    @9
    cI
    cJ
    cN
    cN
    crg
    cX
    cY
    @19
    @20
    eqid
    #
    @12
    eqid
    @0
    @3
    @6
    simp1
    @3
    @0
    @15
    @6
    @1
    @15
    @2
    @1
    @15
    @16
    @18
    simpld
    adantr
    3ad2ant2
    #
    @22
    @22
    @3
    @0
    cX
    @20
    cN
    cN
    cxp
    cmap
    co
    #
    wcel
    #
    @6
    @1
    @24
    @2
    cA
    cB
    cR
    @20
    cX
    cN
    matmulcell.a
    @21
    matmulcell.b
    matbas2i
    adantr
    3ad2ant2
    @3
    @0
    cY
    @23
    wcel
    #
    @6
    @2
    @25
    @1
    cA
    cB
    cR
    @20
    cY
    cN
    matmulcell.a
    @21
    matmulcell.b
    matbas2i
    adantl
    3ad2ant2
    @0
    @3
    @4
    @5
    simp3l
    @0
    @3
    @4
    @5
    simp3r
    mamufv
    eqtrd
end
