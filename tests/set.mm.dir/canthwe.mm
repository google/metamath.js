include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "csdm.mm"
include "cvv.mm"
include "cpw.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wwe.mm"
include "w3a.mm"
include "copab.mm"
include "wa.mm"
include "simp1.mm"
include "selpw.mm"
include "sylibr.mm"
include "simp2.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "jca.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "3sstr4i.mm"
include "pwexg.mm"
include "sqxpexg.mm"
include "syl.mm"
include "xpexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "csn.mm"
include "c0.mm"
include "cop.mm"
include "simpr.mm"
include "snssd.mm"
include "0ss.mm"
include "a1i.mm"
include "wrel.mm"
include "rel0.mm"
include "br0.mm"
include "wesn.mm"
include "mpbiri.mm"
include "mp1i.mm"
include "snex.mm"
include "0ex.mm"
include "wceq.mm"
include "simpl.mm"
include "sseq1d.mm"
include "sqxpeqd.mm"
include "sseq12d.mm"
include "weeq2.mm"
include "weeq1.mm"
include "sylan9bb.mm"
include "3anbi123d.mm"
include "opelopaba.mm"
include "syl3anbrc.mm"
include "syl6eleqr.mm"
include "ex.mm"
include "wb.mm"
include "eqid.mm"
include "opth2.mm"
include "mpbiran2.mm"
include "vex.mm"
include "sneqbg.mm"
include "ax-mp.mm"
include "bitri.mm"
include "2a1i.mm"
include "dom2d.mm"
include "mpd.mm"
include "wf1o.mm"
include "wex.mm"
include "wf1.mm"
include "cin.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "cdm.mm"
include "cuni.mm"
include "cfv.mm"
include "fpwwe2cbv.mm"
include "canthwelem.mm"
include "f1of1.mm"
include "nsyl.mm"
include "nexdv.mm"
include "ensym.mm"
include "bren.mm"
include "sylib.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem canthwe
  let vx: setvar x
  let cA: class A
  let cO: class O
  let cV: class V
  let vr: setvar r
  let vu: setvar u
  let vy: setvar y
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vv: setvar v
  let vw: setvar w
  let va: setvar a
  let vs: setvar s
  let vz: setvar z
  let cF: class F
  let cW: class W
  assume canthwe.1: |- O = { <. x , r >. | ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) }

  disjoint r x
  disjoint O r
  disjoint O x
  disjoint V r
  disjoint V x
  disjoint A r
  disjoint A x
  disjoint r u
  disjoint r y
  disjoint B r
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C r
  disjoint C x
  disjoint f r
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint O f
  disjoint r v
  disjoint r w
  disjoint u v
  disjoint u w
  disjoint O u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint O v
  disjoint w x
  disjoint w y
  disjoint O w
  disjoint O y
  disjoint V f
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V y
  disjoint a f
  disjoint a r
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint f s
  disjoint f z
  disjoint r s
  disjoint r z
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint v z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint a u
  disjoint A a
  disjoint A f
  disjoint s u
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint F r
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint W r
  disjoint W u
  disjoint W x
  disjoint W y
  assert |- ( A e. V -> A ~< O )

  proof
    cA
    cV
    wcel
    #
    cA
    cO
    cdom
    wbr
    #
    cA
    cO
    cen
    wbr
    #
    wn
    cA
    cO
    csdm
    wbr
    @0
    cO
    cvv
    wcel
    #
    @1
    @0
    cO
    cA
    cpw
    #
    cA
    cA
    cxp
    #
    cpw
    #
    cxp
    #
    wss
    @7
    cvv
    wcel
    #
    @3
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @9
    @9
    cxp
    #
    wss
    #
    @9
    @11
    wwe
    #
    w3a
    #
    vx
    vr
    copab
    #
    @9
    @4
    wcel
    #
    @11
    @6
    wcel
    #
    wa
    #
    vx
    vr
    copab
    cO
    @7
    @15
    @19
    vx
    vr
    @15
    @17
    @18
    @15
    @10
    @17
    @10
    @13
    @14
    simp1
    #
    vx
    cA
    selpw
    sylibr
    @15
    @11
    @5
    wss
    @18
    @15
    @11
    @12
    @5
    @10
    @13
    @14
    simp2
    @15
    @10
    @10
    @12
    @5
    wss
    @20
    @20
    @9
    cA
    @9
    cA
    xpss12
    syl2anc
    sstrd
    vr
    @5
    selpw
    sylibr
    jca
    ssopab2i
    canthwe.1
    vx
    vr
    @4
    @6
    df-xp
    3sstr4i
    @0
    @4
    cvv
    wcel
    @6
    cvv
    wcel
    #
    @8
    cA
    cV
    pwexg
    @0
    @5
    cvv
    wcel
    @21
    cA
    cV
    sqxpexg
    @5
    cvv
    pwexg
    syl
    @4
    @6
    cvv
    cvv
    xpexg
    syl2anc
    cO
    @7
    cvv
    ssexg
    sylancr
    @0
    vu
    vv
    cA
    cO
    vu
    cv
    #
    csn
    #
    c0
    cop
    #
    vv
    cv
    #
    csn
    #
    c0
    cop
    #
    cvv
    @0
    @22
    cA
    wcel
    #
    @24
    cO
    wcel
    @0
    @28
    wa
    #
    @24
    @16
    cO
    @29
    @23
    cA
    wss
    #
    c0
    @23
    @23
    cxp
    #
    wss
    #
    @23
    c0
    wwe
    #
    @24
    @16
    wcel
    @29
    @22
    cA
    @0
    @28
    simpr
    snssd
    @32
    @29
    @31
    0ss
    a1i
    c0
    wrel
    #
    @33
    @29
    rel0
    @34
    @33
    @22
    @22
    c0
    wbr
    wn
    @22
    @22
    br0
    @22
    c0
    wesn
    mpbiri
    mp1i
    @15
    @30
    @32
    @33
    w3a
    vx
    vr
    @23
    c0
    @22
    snex
    0ex
    @9
    @23
    wceq
    #
    @11
    c0
    wceq
    #
    wa
    #
    @10
    @30
    @13
    @32
    @14
    @33
    @37
    @9
    @23
    cA
    @35
    @36
    simpl
    #
    sseq1d
    @37
    @11
    c0
    @12
    @31
    @35
    @36
    simpr
    @37
    @9
    @23
    @38
    sqxpeqd
    sseq12d
    @35
    @14
    @23
    @11
    wwe
    @36
    @33
    @9
    @23
    @11
    weeq2
    @23
    @11
    c0
    weeq1
    sylan9bb
    3anbi123d
    opelopaba
    syl3anbrc
    canthwe.1
    syl6eleqr
    ex
    @24
    @27
    wceq
    #
    @22
    @25
    wceq
    #
    wb
    @0
    @28
    @25
    cA
    wcel
    wa
    @39
    @23
    @26
    wceq
    #
    @40
    @39
    @41
    c0
    c0
    wceq
    c0
    eqid
    @23
    c0
    @26
    c0
    @25
    snex
    0ex
    opth2
    mpbiran2
    @22
    cvv
    wcel
    @41
    @40
    wb
    vu
    vex
    @22
    @25
    cvv
    sneqbg
    ax-mp
    bitri
    2a1i
    dom2d
    mpd
    @0
    cO
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @2
    @0
    @43
    vf
    @0
    cO
    cA
    @42
    wf1
    @43
    vx
    vy
    vw
    cA
    va
    cv
    #
    cA
    wss
    vs
    cv
    #
    @45
    @45
    cxp
    wss
    wa
    @45
    @46
    wwe
    @25
    @46
    @25
    @25
    cxp
    cin
    @42
    co
    vz
    cv
    #
    wceq
    vv
    @46
    ccnv
    @47
    csn
    cima
    wsbc
    vz
    @45
    wral
    wa
    wa
    va
    vs
    copab
    #
    cdm
    cuni
    #
    @49
    @48
    cfv
    #
    ccnv
    @49
    @50
    @42
    co
    csn
    cima
    #
    @42
    cO
    cV
    @48
    vr
    canthwe.1
    va
    vz
    vy
    vw
    vv
    cA
    @42
    @48
    vr
    vs
    vx
    @48
    eqid
    fpwwe2cbv
    @49
    eqid
    @51
    eqid
    canthwelem
    cO
    cA
    @42
    f1of1
    nsyl
    nexdv
    @2
    cO
    cA
    cen
    wbr
    @44
    cA
    cO
    ensym
    cO
    cA
    vf
    bren
    sylib
    nsyl
    cA
    cO
    brsdom
    sylanbrc
end
