include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cplt.mm"
include "cfv.mm"
include "eqid.mm"
include "cvrlt.mm"
include "hlrelat3.mm"
include "syldan.mm"
include "simp3l.mm"
include "wb.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2.mm"
include "cvr1.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "latjcl.mm"
include "syl31anc.mm"
include "simp3r.mm"
include "cpo.mm"
include "hlpos.mm"
include "simp1l3.mm"
include "simp1r.mm"
include "cvrnbtwn2.mm"
include "syl131anc.mm"
include "mpbi2and.mm"
include "jca.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"
include "ex.mm"
include "simp11.mm"
include "simp12.mm"
include "mpbid.mm"
include "breqtrd.mm"
include "rexlimdv3a.mm"
include "impbid.mm"

theorem cvrval3
  let cA: class A
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cvrval3.b: |- B = ( Base ` K )
  assume cvrval3.l: |- .<_ = ( le ` K )
  assume cvrval3.j: |- .\/ = ( join ` K )
  assume cvrval3.c: |- C = ( <o ` K )
  assume cvrval3.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint C p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( X C Y <-> E. p e. A ( -. p .<_ X /\ ( X .\/ p ) = Y ) ) )

  proof
    cK
    chlt
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
    w3a
    #
    cX
    cY
    cC
    wbr
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    wn
    #
    cX
    @5
    c.or
    co
    #
    cY
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    #
    @3
    @4
    @10
    @3
    @4
    wa
    #
    cX
    @7
    cC
    wbr
    #
    @7
    cY
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @10
    @3
    @4
    cX
    cY
    cK
    cplt
    cfv
    #
    wbr
    @15
    chlt
    cB
    cC
    @16
    cK
    cX
    cY
    cvrval3.b
    @16
    eqid
    #
    cvrval3.c
    cvrlt
    cA
    cB
    cC
    @16
    c.or
    cK
    c.le
    cX
    cY
    vp
    cvrval3.b
    cvrval3.l
    @17
    cvrval3.j
    cvrval3.c
    cvrval3.a
    hlrelat3
    syldan
    @11
    @14
    @9
    vp
    cA
    @11
    @5
    cA
    wcel
    #
    @14
    @9
    @11
    @18
    @14
    w3a
    #
    @6
    @8
    @19
    @6
    @12
    @11
    @18
    @12
    @13
    simp3l
    #
    @19
    @0
    @1
    @18
    @6
    @12
    wb
    #
    @0
    @1
    @2
    @4
    @18
    @14
    simp1l1
    #
    @0
    @1
    @2
    @4
    @18
    @14
    simp1l2
    #
    @11
    @18
    @14
    simp2
    cA
    cB
    cC
    @5
    c.or
    cK
    c.le
    cX
    cvrval3.b
    cvrval3.l
    cvrval3.j
    cvrval3.c
    cvrval3.a
    cvr1
    #
    syl3anc
    mpbird
    @19
    cX
    @7
    @16
    wbr
    #
    @13
    @8
    @19
    @0
    @1
    @7
    cB
    wcel
    #
    @12
    @25
    @22
    @23
    @19
    cK
    clat
    wcel
    #
    @1
    @5
    cB
    wcel
    #
    @26
    @19
    @0
    @27
    @22
    cK
    hllat
    syl
    @23
    @18
    @11
    @28
    @14
    cA
    cB
    @5
    cK
    cvrval3.b
    cvrval3.a
    atbase
    3ad2ant2
    cB
    c.or
    cK
    cX
    @5
    cvrval3.b
    cvrval3.j
    latjcl
    syl3anc
    #
    @20
    chlt
    cB
    cC
    @16
    cK
    cX
    @7
    cvrval3.b
    @17
    cvrval3.c
    cvrlt
    syl31anc
    @11
    @18
    @12
    @13
    simp3r
    @19
    cK
    cpo
    wcel
    #
    @1
    @2
    @26
    @4
    @25
    @13
    wa
    @8
    wb
    @19
    @0
    @30
    @22
    cK
    hlpos
    syl
    @23
    @0
    @1
    @2
    @4
    @18
    @14
    simp1l3
    @29
    @3
    @4
    @18
    @14
    simp1r
    cB
    cC
    @16
    cK
    c.le
    cX
    cY
    @7
    cvrval3.b
    cvrval3.l
    @17
    cvrval3.c
    cvrnbtwn2
    syl131anc
    mpbi2and
    jca
    3exp
    reximdvai
    mpd
    ex
    @3
    @9
    @4
    vp
    cA
    @3
    @18
    @9
    w3a
    #
    cX
    @7
    cY
    cC
    @31
    @6
    @12
    @3
    @18
    @6
    @8
    simp3l
    @31
    @0
    @1
    @18
    @21
    @0
    @1
    @2
    @18
    @9
    simp11
    @0
    @1
    @2
    @18
    @9
    simp12
    @3
    @18
    @9
    simp2
    @24
    syl3anc
    mpbid
    @3
    @18
    @6
    @8
    simp3r
    breqtrd
    rexlimdv3a
    impbid
end
