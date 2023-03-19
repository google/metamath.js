include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cxp.mm"
include "csn.mm"
include "cof.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "matvsca2.mm"
include "oveqd.mm"
include "3ad2ant2.mm"
include "df-ov.mm"
include "a1i.mm"
include "opelxpi.mm"
include "3ad2ant3.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantl.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "simp2l.mm"
include "cbs.mm"
include "cmap.mm"
include "wfn.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simp1.mm"
include "matbas2.mm"
include "eleqtrrd.mm"
include "elmapfn.mm"
include "syl.mm"
include "eqcomi.mm"
include "ofc1.mm"
include "mpdan.mm"
include "3eqtrd.mm"

theorem matvscacell
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  assume matplusgcell.a: |- A = ( N Mat R )
  assume matplusgcell.b: |- B = ( Base ` A )
  assume matvscacell.k: |- K = ( Base ` R )
  assume matvscacell.v: |- .x. = ( .s ` A )
  assume matvscacell.t: |- .X. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( X e. K /\ Y e. B ) /\ ( I e. N /\ J e. N ) ) -> ( I ( X .x. Y ) J ) = ( X .X. ( I Y J ) ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cK
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
    cJ
    cN
    wcel
    wa
    #
    w3a
    #
    cI
    cJ
    cX
    cY
    c.x
    co
    #
    co
    #
    cI
    cJ
    cN
    cN
    cxp
    #
    cX
    csn
    cxp
    cY
    c.xp
    cof
    co
    #
    co
    #
    cI
    cJ
    cop
    #
    @9
    cfv
    #
    cX
    cI
    cJ
    cY
    co
    #
    c.xp
    co
    #
    @3
    @0
    @7
    @10
    wceq
    @4
    @3
    @6
    @9
    cI
    cJ
    cA
    cB
    @8
    cR
    c.x
    c.xp
    cK
    cN
    cX
    cY
    matplusgcell.a
    matplusgcell.b
    matvscacell.k
    matvscacell.v
    matvscacell.t
    @8
    eqid
    matvsca2
    oveqd
    3ad2ant2
    @10
    @12
    wceq
    @5
    cI
    cJ
    @9
    df-ov
    a1i
    @5
    @11
    @8
    wcel
    #
    @12
    @14
    wceq
    @4
    @0
    @15
    @3
    cI
    cJ
    cN
    cN
    opelxpi
    3ad2ant3
    @5
    @8
    cX
    @13
    c.xp
    cY
    cfn
    cK
    @11
    @5
    cN
    cfn
    wcel
    #
    @16
    @8
    cfn
    wcel
    @3
    @0
    @16
    @4
    @2
    @16
    @1
    @2
    @16
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cY
    matplusgcell.a
    matplusgcell.b
    matrcl
    simpld
    adantl
    3ad2ant2
    #
    @17
    cN
    cN
    xpfi
    syl2anc
    @0
    @1
    @2
    @4
    simp2l
    @5
    cY
    cR
    cbs
    cfv
    #
    @8
    cmap
    co
    #
    wcel
    cY
    @8
    wfn
    @5
    cY
    cA
    cbs
    cfv
    #
    @19
    @3
    @0
    cY
    @20
    wcel
    #
    @4
    @2
    @21
    @1
    @2
    @21
    cB
    @20
    cY
    matplusgcell.b
    eleq2i
    biimpi
    adantl
    3ad2ant2
    @5
    @16
    @0
    @19
    @20
    wceq
    @17
    @0
    @3
    @4
    simp1
    cA
    cR
    @18
    cN
    crg
    matplusgcell.a
    @18
    eqid
    matbas2
    syl2anc
    eleqtrrd
    cY
    @18
    @8
    elmapfn
    syl
    @11
    cY
    cfv
    #
    @13
    wceq
    @5
    @15
    wa
    @13
    @22
    cI
    cJ
    cY
    df-ov
    eqcomi
    a1i
    ofc1
    mpdan
    3eqtrd
end
