include "chlt.mm"
include "wcel.mm"
include "wbr.mm"
include "w3a.mm"
include "coc.mm"
include "cfv.mm"
include "cv.mm"
include "cjn.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "simp1.mm"
include "eqid.mm"
include "1cvrco.mm"
include "biimp3a.mm"
include "2dim.mm"
include "syl2anc.mm"
include "cple.mm"
include "cp0.mm"
include "wne.mm"
include "simp11.mm"
include "cops.mm"
include "hlop.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simp12.mm"
include "opoccl.mm"
include "simp2l.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "op0le.mm"
include "simp3r.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "wb.mm"
include "opltcon3b.mm"
include "mpbid.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "op0cl.mm"
include "plelttr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "pltne.mm"
include "mpd.mm"
include "necomd.mm"
include "atle.mm"
include "simp3l.mm"
include "wceq.mm"
include "opococ.mm"
include "breqtrd.mm"
include "adantr.mm"
include "simpl11.mm"
include "adantl.mm"
include "simpl12.mm"
include "mpan2d.mm"
include "reximdva.mm"
include "3exp.mm"
include "rexlimdvv.mm"

theorem 1cvratex
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let c.1: class .1.
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume 1cvratex.b: |- B = ( Base ` K )
  assume 1cvratex.s: |- .< = ( lt ` K )
  assume 1cvratex.u: |- .1. = ( 1. ` K )
  assume 1cvratex.c: |- C = ( <o ` K )
  assume 1cvratex.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint C p
  disjoint K p
  disjoint .< p
  disjoint .1. p
  disjoint X p
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint B q
  disjoint B r
  disjoint C q
  disjoint C r
  disjoint K q
  disjoint K r
  disjoint .< q
  disjoint .< r
  disjoint .1. q
  disjoint .1. r
  disjoint X q
  disjoint X r
  assert |- ( ( K e. HL /\ X e. B /\ X C .1. ) -> E. p e. A p .< X )

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
    c.1
    cC
    wbr
    #
    w3a
    #
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    @5
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cC
    wbr
    #
    @8
    @8
    vr
    cv
    #
    @7
    co
    #
    cC
    wbr
    #
    wa
    #
    vr
    cA
    wrex
    vq
    cA
    wrex
    #
    vp
    cv
    #
    cX
    c.lt
    wbr
    #
    vp
    cA
    wrex
    #
    @3
    @0
    @5
    cA
    wcel
    #
    @14
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    @18
    cA
    cB
    cC
    c.1
    cK
    @4
    cX
    1cvratex.b
    1cvratex.u
    @4
    eqid
    #
    1cvratex.c
    1cvratex.a
    1cvrco
    biimp3a
    cA
    cC
    @5
    @7
    cK
    vr
    vq
    @7
    eqid
    #
    1cvratex.c
    1cvratex.a
    2dim
    syl2anc
    @3
    @13
    @17
    vq
    vr
    cA
    cA
    @3
    @6
    cA
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    @13
    @17
    @3
    @23
    @13
    w3a
    #
    @15
    @8
    @4
    cfv
    #
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cA
    wrex
    #
    @17
    @24
    @0
    @25
    cB
    wcel
    #
    @25
    cK
    cp0
    cfv
    #
    wne
    @28
    @0
    @1
    @2
    @23
    @13
    simp11
    #
    @24
    cK
    cops
    wcel
    #
    @8
    cB
    wcel
    #
    @29
    @24
    @0
    @32
    @31
    cK
    hlop
    syl
    #
    @24
    cK
    clat
    wcel
    #
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @33
    @24
    @0
    @35
    @31
    cK
    hllat
    syl
    #
    @24
    @32
    @1
    @36
    @34
    @0
    @1
    @2
    @23
    @13
    simp12
    #
    cB
    cK
    @4
    cX
    1cvratex.b
    @19
    opoccl
    syl2anc
    #
    @24
    @21
    @37
    @3
    @21
    @22
    @13
    simp2l
    cA
    cB
    @6
    cK
    1cvratex.b
    1cvratex.a
    atbase
    syl
    cB
    @7
    cK
    @5
    @6
    1cvratex.b
    @20
    latjcl
    syl3anc
    #
    cB
    cK
    @4
    @8
    1cvratex.b
    @19
    opoccl
    syl2anc
    #
    @24
    @30
    @25
    @24
    @30
    @25
    c.lt
    wbr
    #
    @30
    @25
    wne
    #
    @24
    @30
    @11
    @4
    cfv
    #
    @26
    wbr
    #
    @45
    @25
    c.lt
    wbr
    #
    @43
    @24
    @32
    @45
    cB
    wcel
    #
    @46
    @34
    @24
    @32
    @11
    cB
    wcel
    #
    @48
    @34
    @24
    @35
    @33
    @10
    cB
    wcel
    #
    @49
    @38
    @41
    @24
    @22
    @50
    @3
    @21
    @22
    @13
    simp2r
    cA
    cB
    @10
    cK
    1cvratex.b
    1cvratex.a
    atbase
    syl
    cB
    @7
    cK
    @8
    @10
    1cvratex.b
    @20
    latjcl
    syl3anc
    #
    cB
    cK
    @4
    @11
    1cvratex.b
    @19
    opoccl
    syl2anc
    #
    cB
    cK
    @26
    @45
    @30
    1cvratex.b
    @26
    eqid
    #
    @30
    eqid
    #
    op0le
    syl2anc
    @24
    @8
    @11
    c.lt
    wbr
    #
    @47
    @24
    @0
    @33
    @49
    @12
    @55
    @31
    @41
    @51
    @3
    @23
    @9
    @12
    simp3r
    chlt
    cB
    cC
    c.lt
    cK
    @8
    @11
    1cvratex.b
    1cvratex.s
    1cvratex.c
    cvrlt
    syl31anc
    @24
    @32
    @33
    @49
    @55
    @47
    wb
    @34
    @41
    @51
    cB
    c.lt
    cK
    @4
    @8
    @11
    1cvratex.b
    1cvratex.s
    @19
    opltcon3b
    syl3anc
    mpbid
    @24
    cK
    cpo
    wcel
    #
    @30
    cB
    wcel
    #
    @48
    @29
    @46
    @47
    wa
    @43
    wi
    @24
    @0
    @56
    @31
    cK
    hlpos
    #
    syl
    @24
    @32
    @57
    @34
    cB
    cK
    @30
    1cvratex.b
    @54
    op0cl
    syl
    #
    @52
    @42
    cB
    c.lt
    cK
    @26
    @30
    @45
    @25
    1cvratex.b
    @53
    1cvratex.s
    plelttr
    syl13anc
    mp2and
    @24
    @0
    @57
    @29
    @43
    @44
    wi
    @31
    @59
    @42
    chlt
    cB
    cB
    c.lt
    cK
    @30
    @25
    1cvratex.s
    pltne
    syl3anc
    mpd
    necomd
    cA
    cB
    cK
    @26
    @25
    @30
    vp
    1cvratex.b
    @53
    @54
    1cvratex.a
    atle
    syl3anc
    @24
    @27
    @16
    vp
    cA
    @24
    @15
    cA
    wcel
    #
    wa
    #
    @27
    @25
    cX
    c.lt
    wbr
    #
    @16
    @24
    @62
    @60
    @24
    @25
    @5
    @4
    cfv
    #
    cX
    c.lt
    @24
    @5
    @8
    c.lt
    wbr
    #
    @25
    @63
    c.lt
    wbr
    #
    @24
    @0
    @36
    @33
    @9
    @64
    @31
    @40
    @41
    @3
    @23
    @9
    @12
    simp3l
    chlt
    cB
    cC
    c.lt
    cK
    @5
    @8
    1cvratex.b
    1cvratex.s
    1cvratex.c
    cvrlt
    syl31anc
    @24
    @32
    @36
    @33
    @64
    @65
    wb
    @34
    @40
    @41
    cB
    c.lt
    cK
    @4
    @5
    @8
    1cvratex.b
    1cvratex.s
    @19
    opltcon3b
    syl3anc
    mpbid
    @24
    @32
    @1
    @63
    cX
    wceq
    @34
    @39
    cB
    cK
    @4
    cX
    1cvratex.b
    @19
    opococ
    syl2anc
    breqtrd
    adantr
    @61
    @56
    @15
    cB
    wcel
    #
    @29
    @1
    @27
    @62
    wa
    @16
    wi
    @61
    @0
    @56
    @0
    @1
    @2
    @23
    @13
    @60
    simpl11
    @58
    syl
    @60
    @66
    @24
    cA
    cB
    @15
    cK
    1cvratex.b
    1cvratex.a
    atbase
    adantl
    @24
    @29
    @60
    @42
    adantr
    @0
    @1
    @2
    @23
    @13
    @60
    simpl12
    cB
    c.lt
    cK
    @26
    @15
    @25
    cX
    1cvratex.b
    @53
    1cvratex.s
    plelttr
    syl13anc
    mpan2d
    reximdva
    mpd
    3exp
    rexlimdvv
    mpd
end
