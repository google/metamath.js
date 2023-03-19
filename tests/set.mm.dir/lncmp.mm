include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "catm.mm"
include "wrex.mm"
include "simplrl.mm"
include "wb.mm"
include "simpll1.mm"
include "simpll2.mm"
include "eqid.mm"
include "isline3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp3rr.mm"
include "simp1l1.mm"
include "simp1l3.mm"
include "simp1rr.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "simp3rl.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "simp1l2.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "breqtrrd.mm"
include "simp2.mm"
include "lattrd.mm"
include "hlatlej2.mm"
include "lneq2at.mm"
include "syl332anc.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "ex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "latref.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem lncmp
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  assume lncmp.b: |- B = ( Base ` K )
  assume lncmp.l: |- .<_ = ( le ` K )
  assume lncmp.n: |- N = ( Lines ` K )
  assume lncmp.m: |- M = ( pmap ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( ( M ` X ) e. N /\ ( M ` Y ) e. N ) ) -> ( X .<_ Y <-> X = Y ) )

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
    cM
    cfv
    cN
    wcel
    #
    cY
    cM
    cfv
    cN
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wceq
    #
    @7
    @8
    @9
    @7
    @8
    wa
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cX
    @11
    @12
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vq
    cK
    catm
    cfv
    #
    wrex
    vp
    @18
    wrex
    #
    @9
    @10
    @4
    @19
    @3
    @4
    @5
    @8
    simplrl
    @10
    @0
    @1
    @4
    @19
    wb
    @0
    @1
    @2
    @6
    @8
    simpll1
    @0
    @1
    @2
    @6
    @8
    simpll2
    @18
    cB
    @14
    cK
    cM
    cN
    cX
    vq
    vp
    lncmp.b
    @14
    eqid
    #
    @18
    eqid
    #
    lncmp.n
    lncmp.m
    isline3
    syl2anc
    mpbid
    @10
    @17
    @9
    vp
    vq
    @18
    @18
    @10
    @11
    @18
    wcel
    #
    @12
    @18
    wcel
    #
    wa
    #
    @17
    @9
    @7
    @8
    @24
    @17
    wa
    #
    @9
    @7
    @8
    @25
    w3a
    #
    cX
    @15
    cY
    @13
    @16
    @24
    @7
    @8
    simp3rr
    #
    @26
    @0
    @2
    @5
    @22
    @23
    @13
    @11
    cY
    c.le
    wbr
    @12
    cY
    c.le
    wbr
    cY
    @15
    wceq
    @0
    @1
    @2
    @6
    @8
    @25
    simp1l1
    #
    @0
    @1
    @2
    @6
    @8
    @25
    simp1l3
    #
    @4
    @5
    @3
    @8
    @25
    simp1rr
    @22
    @23
    @17
    @7
    @8
    simp3ll
    #
    @22
    @23
    @17
    @7
    @8
    simp3lr
    #
    @13
    @16
    @24
    @7
    @8
    simp3rl
    @26
    cB
    cK
    c.le
    @11
    cX
    cY
    lncmp.b
    lncmp.l
    @26
    @0
    cK
    clat
    wcel
    #
    @28
    cK
    hllat
    #
    syl
    #
    @26
    @22
    @11
    cB
    wcel
    @30
    @18
    cB
    @11
    cK
    lncmp.b
    @21
    atbase
    syl
    @0
    @1
    @2
    @6
    @8
    @25
    simp1l2
    #
    @29
    @26
    @11
    @15
    cX
    c.le
    @26
    @0
    @22
    @23
    @11
    @15
    c.le
    wbr
    @28
    @30
    @31
    @18
    @11
    @12
    @14
    cK
    c.le
    lncmp.l
    @20
    @21
    hlatlej1
    syl3anc
    @27
    breqtrrd
    @7
    @8
    @25
    simp2
    #
    lattrd
    @26
    cB
    cK
    c.le
    @12
    cX
    cY
    lncmp.b
    lncmp.l
    @34
    @26
    @23
    @12
    cB
    wcel
    @31
    @18
    cB
    @12
    cK
    lncmp.b
    @21
    atbase
    syl
    @35
    @29
    @26
    @12
    @15
    cX
    c.le
    @26
    @0
    @22
    @23
    @12
    @15
    c.le
    wbr
    @28
    @30
    @31
    @18
    @11
    @12
    @14
    cK
    c.le
    lncmp.l
    @20
    @21
    hlatlej2
    syl3anc
    @27
    breqtrrd
    @36
    lattrd
    @18
    cB
    @11
    @12
    @14
    cK
    c.le
    cM
    cN
    cY
    lncmp.b
    lncmp.l
    @20
    @21
    lncmp.n
    lncmp.m
    lneq2at
    syl332anc
    eqtr4d
    3expia
    expd
    rexlimdvv
    mpd
    ex
    @7
    cX
    cX
    c.le
    wbr
    #
    @9
    @8
    @7
    @32
    @1
    @37
    @7
    @0
    @32
    @0
    @1
    @2
    @6
    simpl1
    @33
    syl
    @0
    @1
    @2
    @6
    simpl2
    cB
    cK
    c.le
    cX
    lncmp.b
    lncmp.l
    latref
    syl2anc
    cX
    cY
    cX
    c.le
    breq2
    syl5ibcom
    impbid
end
