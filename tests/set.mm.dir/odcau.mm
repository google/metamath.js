include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "cprime.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "csubg.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cn0.mm"
include "1nn0.mm"
include "a1i.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "nncnd.mm"
include "exp1d.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "sylow1.mm"
include "wb.mm"
include "eqeq2d.mm"
include "adantr.mm"
include "wex.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "csdm.mm"
include "clt.mm"
include "cvv.mm"
include "fvex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "c2.mm"
include "cuz.mm"
include "simprr.mm"
include "prmuz2.mm"
include "eqeltrd.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "syl5eqbr.mm"
include "snfi.mm"
include "wss.mm"
include "subgss.mm"
include "ad2antrl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashsdom.mm"
include "sylancr.mm"
include "mpbid.mm"
include "sdomdif.mm"
include "n0.mm"
include "sylib.mm"
include "eldifsn.mm"
include "adantrr.mm"
include "simprrl.mm"
include "sseldd.mm"
include "simprrr.mm"
include "wn.mm"
include "wo.mm"
include "simprll.mm"
include "odsubdvds.mm"
include "syl3anc.mm"
include "simprlr.mm"
include "breqtrd.mm"
include "odcl2.mm"
include "dvdsprime.mm"
include "ord.mm"
include "eqid.mm"
include "odeq1.mm"
include "sylibd.mm"
include "necon1ad.mm"
include "mpd.mm"
include "jca.mm"
include "expr.mm"
include "syl5bi.mm"
include "eximdv.mm"
include "df-rex.mm"
include "sylibr.mm"
include "sylbid.mm"
include "rexlimdva.mm"

theorem odcau
  let cP: class P
  let vg: setvar g
  let cG: class G
  let cO: class O
  let cX: class X
  let vs: setvar s
  assume odcau.x: |- X = ( Base ` G )
  assume odcau.o: |- O = ( od ` G )

  disjoint G g
  disjoint P g
  disjoint X g
  disjoint g s
  disjoint G s
  disjoint O s
  disjoint P s
  disjoint X s
  assert |- ( ( ( G e. Grp /\ X e. Fin /\ P e. Prime ) /\ P || ( # ` X ) ) -> E. g e. X ( O ` g ) = P )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cP
    cX
    chash
    cfv
    #
    cdvds
    wbr
    #
    wa
    #
    vs
    cv
    #
    chash
    cfv
    #
    cP
    c1
    cexp
    co
    #
    wceq
    #
    vs
    cG
    csubg
    cfv
    #
    wrex
    vg
    cv
    #
    cO
    cfv
    #
    cP
    wceq
    #
    vg
    cX
    wrex
    #
    @6
    cP
    vs
    cG
    c1
    cX
    odcau.x
    @0
    @1
    @2
    @5
    simpl1
    #
    @0
    @1
    @2
    @5
    simpl2
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    c1
    cn0
    wcel
    @6
    1nn0
    a1i
    @6
    @9
    cP
    @4
    cdvds
    @6
    cP
    @6
    cP
    @6
    @2
    cP
    cn
    wcel
    @18
    cP
    prmnn
    syl
    nncnd
    exp1d
    #
    @3
    @5
    simpr
    eqbrtrd
    sylow1
    @6
    @10
    @15
    vs
    @11
    @6
    @7
    @11
    wcel
    #
    wa
    @10
    @8
    cP
    wceq
    #
    @15
    @6
    @10
    @21
    wb
    @20
    @6
    @9
    cP
    @8
    @19
    eqeq2d
    adantr
    @6
    @20
    @21
    @15
    @6
    @20
    @21
    wa
    #
    wa
    #
    @12
    cX
    wcel
    #
    @14
    wa
    #
    vg
    wex
    #
    @15
    @23
    @12
    @7
    cG
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wcel
    #
    vg
    wex
    #
    @26
    @23
    @29
    c0
    wne
    #
    @31
    @23
    @28
    @7
    csdm
    wbr
    #
    @32
    @23
    @28
    chash
    cfv
    #
    @8
    clt
    wbr
    #
    @33
    @23
    @34
    c1
    @8
    clt
    @27
    cvv
    wcel
    @34
    c1
    wceq
    cG
    c0g
    fvex
    @27
    cvv
    hashsng
    ax-mp
    @23
    @8
    c2
    cuz
    cfv
    #
    wcel
    #
    c1
    @8
    clt
    wbr
    #
    @23
    @8
    cP
    @36
    @6
    @20
    @21
    simprr
    @23
    @2
    cP
    @36
    wcel
    @6
    @2
    @22
    @18
    adantr
    cP
    prmuz2
    syl
    eqeltrd
    @37
    @8
    cn
    wcel
    @38
    @8
    eluz2b2
    simprbi
    syl
    syl5eqbr
    @23
    @28
    cfn
    wcel
    @7
    cfn
    wcel
    #
    @35
    @33
    wb
    @27
    snfi
    @23
    @1
    @7
    cX
    wss
    #
    @39
    @6
    @1
    @22
    @17
    adantr
    @20
    @40
    @6
    @21
    cX
    @7
    cG
    odcau.x
    subgss
    ad2antrl
    #
    cX
    @7
    ssfi
    syl2anc
    #
    @28
    @7
    hashsdom
    sylancr
    mpbid
    @28
    @7
    sdomdif
    syl
    vg
    @29
    n0
    sylib
    @23
    @30
    @25
    vg
    @30
    @12
    @7
    wcel
    #
    @12
    @27
    wne
    #
    wa
    #
    @23
    @25
    @12
    @7
    @27
    eldifsn
    @6
    @22
    @45
    @25
    @6
    @22
    @45
    wa
    #
    wa
    #
    @24
    @14
    @47
    @7
    cX
    @12
    @6
    @22
    @40
    @45
    @41
    adantrr
    @6
    @22
    @43
    @44
    simprrl
    #
    sseldd
    #
    @47
    @44
    @14
    @6
    @22
    @43
    @44
    simprrr
    @47
    @14
    @12
    @27
    @47
    @14
    wn
    @13
    c1
    wceq
    #
    @12
    @27
    wceq
    #
    @47
    @14
    @50
    @47
    @13
    cP
    cdvds
    wbr
    #
    @14
    @50
    wo
    #
    @47
    @13
    @8
    cP
    cdvds
    @47
    @20
    @39
    @43
    @13
    @8
    cdvds
    wbr
    @6
    @20
    @21
    @45
    simprll
    @6
    @22
    @39
    @45
    @42
    adantrr
    @48
    @12
    @7
    cG
    cO
    odcau.o
    odsubdvds
    syl3anc
    @6
    @20
    @21
    @45
    simprlr
    breqtrd
    @47
    @2
    @13
    cn
    wcel
    #
    @52
    @53
    wb
    @6
    @2
    @46
    @18
    adantr
    @47
    @0
    @1
    @24
    @54
    @6
    @0
    @46
    @16
    adantr
    #
    @6
    @1
    @46
    @17
    adantr
    @49
    @12
    cG
    cO
    cX
    odcau.x
    odcau.o
    odcl2
    syl3anc
    cP
    @13
    dvdsprime
    syl2anc
    mpbid
    ord
    @47
    @0
    @24
    @50
    @51
    wb
    @55
    @49
    @12
    cG
    cO
    cX
    @27
    odcau.o
    @27
    eqid
    odcau.x
    odeq1
    syl2anc
    sylibd
    necon1ad
    mpd
    jca
    expr
    syl5bi
    eximdv
    mpd
    @14
    vg
    cX
    df-rex
    sylibr
    expr
    sylbid
    rexlimdva
    mpd
end
