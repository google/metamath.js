include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "weq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "c1.mm"
include "cif.mm"
include "0re.mm"
include "1re.mm"
include "keepel.mm"
include "rgen2w.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "equequ1.mm"
include "ifbid.mm"
include "equequ2.mm"
include "cn0.mm"
include "0nn0.mm"
include "1nn0.mm"
include "elexi.mm"
include "ovmpt2.mm"
include "eqeq1d.mm"
include "wn.mm"
include "iffalse.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "con4i.mm"
include "iftrue.mm"
include "impbii.mm"
include "syl6bb.mm"
include "cn.mm"
include "wo.mm"
include "nn0addcli.mm"
include "elnn0.mm"
include "breq1.mm"
include "0le1.mm"
include "leidi.mm"
include "keephyp.mm"
include "nnge1.mm"
include "nn0rei.mm"
include "letri.mm"
include "sylancr.mm"
include "nn0ge0i.mm"
include "add20i.mm"
include "mp2an.mm"
include "bibi12d.mm"
include "chvarv.mm"
include "eqtr2.mm"
include "syl2anb.mm"
include "iftrued.mm"
include "syl6eqbr.mm"
include "sylbi.mm"
include "id.mm"
include "breqtrrd.mm"
include "jaoi.mm"
include "mp1i.mm"
include "adantl.mm"
include "eqeq12.mm"
include "ovmpt2a.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "expcom.mm"
include "ralrimiv.mm"
include "jca.mm"
include "rgen2a.mm"
include "pm3.2i.mm"
include "ismet.mm"
include "mpbiri.mm"

theorem dscmet
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume dscmet.1: |- D = ( x e. X , y e. X |-> if ( x = y , 0 , 1 ) )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint u v
  disjoint u w
  disjoint D u
  disjoint v w
  disjoint D v
  disjoint D w
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint v x
  disjoint v y
  disjoint X v
  disjoint w x
  disjoint w y
  disjoint X w
  assert |- ( X e. V -> D e. ( Met ` X ) )

  proof
    cX
    cV
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cX
    cX
    cxp
    cr
    cD
    wf
    #
    vw
    cv
    #
    vv
    cv
    #
    cD
    co
    #
    cc0
    wceq
    #
    vw
    vv
    weq
    #
    wb
    #
    @3
    vu
    cv
    #
    @1
    cD
    co
    #
    @7
    @2
    cD
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vu
    cX
    wral
    #
    wa
    #
    vv
    cX
    wral
    vw
    cX
    wral
    #
    wa
    @0
    @14
    vx
    vy
    weq
    #
    cc0
    c1
    cif
    #
    cr
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @0
    @17
    vx
    vy
    cX
    cX
    @15
    cc0
    c1
    cr
    0re
    1re
    keepel
    rgen2w
    vx
    vy
    cX
    cX
    @16
    cr
    cD
    dscmet.1
    fmpt2
    mpbi
    @13
    vw
    vv
    cX
    @1
    cX
    wcel
    #
    @2
    cX
    wcel
    #
    wa
    #
    @6
    @12
    @20
    @4
    @5
    cc0
    c1
    cif
    #
    cc0
    wceq
    #
    @5
    @20
    @3
    @21
    cc0
    vx
    vy
    @1
    @2
    cX
    cX
    @16
    @21
    cD
    vw
    vy
    weq
    #
    cc0
    c1
    cif
    vx
    vw
    weq
    @15
    @23
    cc0
    c1
    vx
    vw
    vy
    equequ1
    ifbid
    vy
    vv
    weq
    #
    @23
    @5
    cc0
    c1
    vy
    vv
    vw
    equequ2
    ifbid
    dscmet.1
    @21
    cn0
    @5
    cc0
    c1
    cn0
    0nn0
    1nn0
    keepel
    #
    elexi
    ovmpt2
    #
    eqeq1d
    @22
    @5
    @5
    @22
    @5
    wn
    #
    @21
    cc0
    @27
    @21
    c1
    cc0
    @5
    cc0
    c1
    iffalse
    c1
    cc0
    wne
    @27
    ax-1ne0
    a1i
    eqnetrd
    neneqd
    con4i
    @5
    cc0
    c1
    iftrue
    impbii
    #
    syl6bb
    @20
    @11
    vu
    cX
    @7
    cX
    wcel
    #
    @20
    @11
    @29
    @20
    wa
    #
    @21
    vu
    vw
    weq
    #
    cc0
    c1
    cif
    #
    vu
    vv
    weq
    #
    cc0
    c1
    cif
    #
    caddc
    co
    #
    @3
    @10
    cle
    @35
    cn
    wcel
    #
    @35
    cc0
    wceq
    #
    wo
    #
    @21
    @35
    cle
    wbr
    #
    @30
    @35
    cn0
    wcel
    @38
    @32
    @34
    @31
    cc0
    c1
    cn0
    0nn0
    1nn0
    keepel
    #
    @33
    cc0
    c1
    cn0
    0nn0
    1nn0
    keepel
    #
    nn0addcli
    #
    @35
    elnn0
    mpbi
    @36
    @39
    @37
    @36
    @21
    c1
    cle
    wbr
    #
    c1
    @35
    cle
    wbr
    @39
    @5
    cc0
    c1
    cle
    wbr
    c1
    c1
    cle
    wbr
    @43
    cc0
    c1
    cc0
    @21
    c1
    cle
    breq1
    c1
    @21
    c1
    cle
    breq1
    0le1
    c1
    1re
    leidi
    keephyp
    @35
    nnge1
    @21
    c1
    @35
    @21
    @25
    nn0rei
    1re
    @35
    @42
    nn0rei
    letri
    sylancr
    @37
    @21
    cc0
    @35
    cle
    @37
    @32
    cc0
    wceq
    #
    @34
    cc0
    wceq
    #
    wa
    #
    @21
    cc0
    cle
    wbr
    cc0
    @32
    cle
    wbr
    cc0
    @34
    cle
    wbr
    @37
    @46
    wb
    @32
    @40
    nn0ge0i
    @34
    @41
    nn0ge0i
    @32
    @34
    @32
    @40
    nn0rei
    @34
    @41
    nn0rei
    add20i
    mp2an
    @46
    @21
    cc0
    cc0
    cle
    @46
    @5
    cc0
    c1
    @44
    @31
    @33
    @5
    @45
    @45
    @33
    wb
    #
    @44
    @31
    wb
    vv
    vw
    vv
    vw
    weq
    #
    @45
    @44
    @33
    @31
    @48
    @34
    @32
    cc0
    @48
    @33
    @31
    cc0
    c1
    vv
    vw
    vu
    equequ2
    #
    ifbid
    eqeq1d
    @49
    bibi12d
    @22
    @5
    wb
    @47
    vw
    vu
    vw
    vu
    weq
    #
    @22
    @45
    @5
    @33
    @50
    @21
    @34
    cc0
    @50
    @5
    @33
    cc0
    c1
    vw
    vu
    vv
    equequ1
    #
    ifbid
    eqeq1d
    @51
    bibi12d
    @28
    chvarv
    #
    chvarv
    @52
    @7
    @1
    @2
    eqtr2
    syl2anb
    iftrued
    cc0
    0re
    leidi
    syl6eqbr
    sylbi
    @37
    id
    breqtrrd
    jaoi
    mp1i
    @20
    @3
    @21
    wceq
    @29
    @26
    adantl
    @30
    @8
    @32
    @9
    @34
    caddc
    @29
    @18
    @8
    @32
    wceq
    @19
    vx
    vy
    @7
    @1
    cX
    cX
    @16
    @32
    cD
    vx
    vu
    weq
    #
    vy
    vw
    weq
    wa
    @15
    @31
    cc0
    c1
    vx
    cv
    #
    @7
    vy
    cv
    #
    @1
    eqeq12
    ifbid
    dscmet.1
    @32
    cn0
    @40
    elexi
    ovmpt2a
    adantrr
    @29
    @19
    @9
    @34
    wceq
    @18
    vx
    vy
    @7
    @2
    cX
    cX
    @16
    @34
    cD
    @53
    @24
    wa
    @15
    @33
    cc0
    c1
    @54
    @7
    @55
    @2
    eqeq12
    ifbid
    dscmet.1
    @34
    cn0
    @41
    elexi
    ovmpt2a
    adantrl
    oveq12d
    3brtr4d
    expcom
    ralrimiv
    jca
    rgen2a
    pm3.2i
    vw
    vv
    vu
    cV
    cD
    cX
    ismet
    mpbiri
end
