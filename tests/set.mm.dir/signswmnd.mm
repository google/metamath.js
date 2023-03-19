include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cif.mm"
include "signspval.mm"
include "ifcl.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "stoic3.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "adantr.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "simp1.mm"
include "3adant1.mm"
include "simpl2.mm"
include "wn.mm"
include "simpl3.mm"
include "ifclda.mm"
include "syl2anc.mm"
include "id.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "ad2antlr.mm"
include "iffalse.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "mtbird.mm"
include "iffalsed.mm"
include "pm2.61dan.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "jca.mm"
include "rgen2a.mm"
include "c0ex.mm"
include "tpid2.mm"
include "signsw0glem.mm"
include "oveq1.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "signswbase.mm"
include "signswplusg.mm"
include "ismnd.mm"
include "mpbir2an.mm"

theorem signswmnd
  let c.pd: class .+^
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let ve: setvar e
  let vv: setvar v
  let vw: setvar w
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }

  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint a u
  disjoint b u
  disjoint e u
  disjoint .+^ e
  disjoint .+^ u
  disjoint W e
  disjoint W u
  disjoint a e
  disjoint a v
  disjoint a w
  disjoint b e
  disjoint b v
  disjoint b w
  disjoint e v
  disjoint e w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint .+^ v
  disjoint .+^ w
  disjoint W v
  disjoint W w
  assert |- W e. Mnd

  proof
    cW
    cmnd
    wcel
    vu
    cv
    #
    vv
    cv
    #
    c.pd
    co
    #
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    wcel
    #
    @2
    vw
    cv
    #
    c.pd
    co
    #
    @0
    @1
    @6
    c.pd
    co
    #
    c.pd
    co
    #
    wceq
    #
    vw
    @4
    wral
    #
    wa
    #
    vv
    @4
    wral
    vu
    @4
    wral
    ve
    cv
    #
    @0
    c.pd
    co
    #
    @0
    wceq
    #
    @0
    @13
    c.pd
    co
    #
    @0
    wceq
    #
    wa
    #
    vu
    @4
    wral
    #
    ve
    @4
    wrex
    #
    @12
    vu
    vv
    @4
    @0
    @4
    wcel
    #
    @1
    @4
    wcel
    #
    wa
    #
    @5
    @11
    @23
    @2
    @1
    cc0
    wceq
    #
    @0
    @1
    cif
    #
    @4
    c.pd
    @0
    @1
    va
    vb
    signsw.p
    signspval
    #
    @24
    @0
    @1
    @4
    ifcl
    eqeltrd
    #
    @23
    @10
    vw
    @4
    @21
    @22
    @6
    @4
    wcel
    #
    @10
    @21
    @22
    @28
    w3a
    #
    @6
    cc0
    wceq
    #
    @10
    @29
    @30
    wa
    #
    @24
    @10
    @31
    @24
    wa
    #
    @7
    @0
    @9
    @32
    @7
    @2
    @25
    @0
    @31
    @7
    @2
    wceq
    @24
    @29
    @30
    @7
    @30
    @2
    @6
    cif
    #
    @2
    @21
    @22
    @5
    @28
    @7
    @33
    wceq
    #
    @27
    c.pd
    @2
    @6
    va
    vb
    signsw.p
    signspval
    stoic3
    #
    @30
    @2
    @6
    iftrue
    #
    sylan9eq
    adantr
    @29
    @2
    @25
    wceq
    #
    @30
    @24
    @21
    @22
    @37
    @28
    @26
    3adant3
    #
    ad2antrr
    @24
    @25
    @0
    wceq
    @31
    @24
    @0
    @1
    iftrue
    adantl
    3eqtrd
    @32
    @9
    @8
    cc0
    wceq
    #
    @0
    @8
    cif
    #
    @0
    @29
    @9
    @40
    wceq
    #
    @30
    @24
    @29
    @21
    @8
    @4
    wcel
    @41
    @21
    @22
    @28
    simp1
    @29
    @8
    @30
    @1
    @6
    cif
    #
    @4
    @22
    @28
    @8
    @42
    wceq
    #
    @21
    c.pd
    @1
    @6
    va
    vb
    signsw.p
    signspval
    3adant1
    #
    @29
    @30
    @1
    @6
    @4
    @21
    @22
    @28
    @30
    simpl2
    @21
    @22
    @28
    @30
    wn
    #
    simpl3
    ifclda
    eqeltrd
    c.pd
    @0
    @8
    va
    vb
    signsw.p
    signspval
    syl2anc
    #
    ad2antrr
    @32
    @39
    @0
    @8
    @31
    @24
    @8
    @1
    cc0
    @29
    @30
    @8
    @42
    @1
    @44
    @30
    @1
    @6
    iftrue
    #
    sylan9eq
    @24
    id
    sylan9eq
    iftrued
    eqtrd
    eqtr4d
    @31
    @24
    wn
    #
    wa
    #
    @7
    @1
    @9
    @49
    @7
    @33
    @2
    @1
    @29
    @34
    @30
    @48
    @35
    ad2antrr
    @30
    @33
    @2
    wceq
    @29
    @48
    @36
    ad2antlr
    @49
    @2
    @25
    @1
    @29
    @37
    @30
    @48
    @38
    ad2antrr
    @48
    @25
    @1
    wceq
    @31
    @24
    @0
    @1
    iffalse
    adantl
    eqtrd
    3eqtrd
    @49
    @9
    @40
    @8
    @1
    @29
    @41
    @30
    @48
    @46
    ad2antrr
    @49
    @39
    @0
    @8
    @49
    @39
    @24
    @31
    @48
    simpr
    @49
    @8
    @1
    cc0
    @49
    @8
    @42
    @1
    @29
    @43
    @30
    @48
    @44
    ad2antrr
    @30
    @42
    @1
    wceq
    @29
    @48
    @47
    ad2antlr
    eqtrd
    #
    eqeq1d
    mtbird
    iffalsed
    @50
    3eqtrd
    eqtr4d
    pm2.61dan
    @29
    @45
    wa
    #
    @7
    @6
    @9
    @29
    @45
    @7
    @33
    @6
    @35
    @30
    @2
    @6
    iffalse
    sylan9eq
    @51
    @9
    @40
    @8
    @6
    @29
    @41
    @45
    @46
    adantr
    @51
    @39
    @0
    @8
    @51
    @39
    @30
    @29
    @45
    simpr
    @51
    @8
    @6
    cc0
    @29
    @45
    @8
    @42
    @6
    @44
    @30
    @1
    @6
    iffalse
    sylan9eq
    #
    eqeq1d
    mtbird
    iffalsed
    @52
    3eqtrd
    eqtr4d
    pm2.61dan
    3expa
    ralrimiva
    jca
    rgen2a
    cc0
    @4
    wcel
    cc0
    @0
    c.pd
    co
    #
    @0
    wceq
    #
    @0
    cc0
    c.pd
    co
    #
    @0
    wceq
    #
    wa
    #
    vu
    @4
    wral
    #
    @20
    @3
    cc0
    c1
    c0ex
    tpid2
    vu
    c.pd
    va
    vb
    signsw.p
    signsw0glem
    @19
    @58
    ve
    cc0
    @4
    @13
    cc0
    wceq
    #
    @18
    @57
    vu
    @4
    @59
    @15
    @54
    @17
    @56
    @59
    @14
    @53
    @0
    @13
    cc0
    @0
    c.pd
    oveq1
    eqeq1d
    @59
    @16
    @55
    @0
    @13
    cc0
    @0
    c.pd
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    mp2an
    @4
    c.pd
    ve
    cW
    vu
    vv
    vw
    c.pd
    cW
    va
    vb
    signsw.p
    signsw.w
    signswbase
    c.pd
    cW
    va
    vb
    signsw.p
    signsw.w
    signswplusg
    ismnd
    mpbir2an
end
