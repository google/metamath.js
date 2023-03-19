include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cplt.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "simp1.mm"
include "cops.mm"
include "hlop.mm"
include "3ad2ant1.mm"
include "op0cl.mm"
include "syl.mm"
include "simp2.mm"
include "simp3.mm"
include "wb.mm"
include "eqid.mm"
include "opltn0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "hlrelat.mm"
include "syl31anc.mm"
include "col.mm"
include "wceq.mm"
include "simpl1.mm"
include "hlol.mm"
include "atbase.mm"
include "adantl.mm"
include "olj02.mm"
include "breq1d.mm"
include "biimpd.mm"
include "adantld.mm"
include "reximdva.mm"
include "mpd.mm"

theorem atle
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  assume atle.b: |- B = ( Base ` K )
  assume atle.l: |- .<_ = ( le ` K )
  assume atle.z: |- .0. = ( 0. ` K )
  assume atle.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint .0. p
  assert |- ( ( K e. HL /\ X e. B /\ X =/= .0. ) -> E. p e. A p .<_ X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    w3a
    #
    c.0
    c.0
    vp
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cplt
    cfv
    #
    wbr
    #
    @6
    cX
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @4
    cX
    c.le
    wbr
    #
    vp
    cA
    wrex
    @3
    @0
    c.0
    cB
    wcel
    #
    @1
    c.0
    cX
    @7
    wbr
    #
    @11
    @0
    @1
    @2
    simp1
    @3
    cK
    cops
    wcel
    #
    @13
    @0
    @1
    @15
    @2
    cK
    hlop
    3ad2ant1
    #
    cB
    cK
    c.0
    atle.b
    atle.z
    op0cl
    syl
    @0
    @1
    @2
    simp2
    #
    @3
    @14
    @2
    @0
    @1
    @2
    simp3
    @3
    @15
    @1
    @14
    @2
    wb
    @16
    @17
    cB
    @7
    cK
    cX
    c.0
    atle.b
    @7
    eqid
    #
    atle.z
    opltn0
    syl2anc
    mpbird
    cA
    cB
    @7
    @5
    cK
    c.le
    c.0
    cX
    vp
    atle.b
    atle.l
    @18
    @5
    eqid
    #
    atle.a
    hlrelat
    syl31anc
    @3
    @10
    @12
    vp
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @9
    @12
    @8
    @21
    @9
    @12
    @21
    @6
    @4
    cX
    c.le
    @21
    cK
    col
    wcel
    #
    @4
    cB
    wcel
    #
    @6
    @4
    wceq
    @21
    @0
    @22
    @0
    @1
    @2
    @20
    simpl1
    cK
    hlol
    syl
    @20
    @23
    @3
    cA
    cB
    @4
    cK
    atle.b
    atle.a
    atbase
    adantl
    cB
    @5
    cK
    @4
    c.0
    atle.b
    @19
    atle.z
    olj02
    syl2anc
    breq1d
    biimpd
    adantld
    reximdva
    mpd
end
