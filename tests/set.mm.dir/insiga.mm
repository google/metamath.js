include "c0.mm"
include "wne.mm"
include "csiga.mm"
include "cfv.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "cint.mm"
include "cvv.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "intex.mm"
include "biimpi.mm"
include "adantr.mm"
include "intssuni.mm"
include "simpr.mm"
include "elpwi.mm"
include "sigasspw.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylib.mm"
include "sstrd.mm"
include "simplr.mm"
include "elelpwi.mm"
include "syl2anc.mm"
include "wb.mm"
include "vex.mm"
include "issiga.mm"
include "ax-mp.mm"
include "simprd.mm"
include "simp1d.mm"
include "ralrimiva.mm"
include "wex.mm"
include "n0.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "elfvex.mm"
include "exlimiv.mm"
include "elintg.mm"
include "mpbird.mm"
include "simpll.mm"
include "jca.mm"
include "elinti.mm"
include "imp.mm"
include "adantll.mm"
include "simp2d.mm"
include "r19.21bi.mm"
include "difexg.mm"
include "simplll.mm"
include "simpllr.mm"
include "intss1.mm"
include "sylan9ss.mm"
include "sylancom.mm"
include "simp3d.mm"
include "sylc.mm"
include "uniexg.mm"
include "ad2antlr.mm"
include "3jca.mm"
include "biimpar.mm"
include "syl12anc.mm"

theorem insiga
  let cA: class A
  let cO: class O
  let vs: setvar s
  let vx: setvar x


  assert |- ( ( A =/= (/) /\ A e. ~P ( sigAlgebra ` O ) ) -> |^| A e. ( sigAlgebra ` O ) )

  proof
    cA
    c0
    wne
    #
    cA
    cO
    csiga
    cfv
    #
    cpw
    wcel
    #
    wa
    #
    cA
    cint
    #
    cvv
    wcel
    #
    @4
    cO
    cpw
    #
    wss
    #
    cO
    @4
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @4
    wcel
    #
    vx
    @4
    wral
    #
    @9
    com
    cdom
    wbr
    #
    @9
    cuni
    #
    @4
    wcel
    #
    wi
    #
    vx
    @4
    cpw
    #
    wral
    #
    w3a
    #
    @4
    @1
    wcel
    #
    @0
    @5
    @2
    @0
    @5
    cA
    intex
    biimpi
    adantr
    @3
    @4
    cA
    cuni
    #
    @6
    @0
    @4
    @21
    wss
    @2
    cA
    intssuni
    adantr
    @3
    cA
    @6
    cpw
    #
    wss
    #
    @21
    @6
    wss
    @3
    @2
    @23
    @0
    @2
    simpr
    @2
    cA
    @1
    @22
    cA
    @1
    elpwi
    vs
    @1
    @22
    vs
    cv
    #
    @1
    wcel
    #
    @24
    @6
    wss
    #
    @24
    @22
    wcel
    cO
    @24
    sigasspw
    vs
    @6
    selpw
    sylibr
    ssriv
    syl6ss
    syl
    cA
    @6
    sspwuni
    sylib
    sstrd
    @3
    @8
    @12
    @18
    @3
    @8
    cO
    @24
    wcel
    #
    vs
    cA
    wral
    #
    @3
    @27
    vs
    cA
    @3
    @24
    cA
    wcel
    #
    wa
    #
    @27
    @10
    @24
    wcel
    #
    vx
    @24
    wral
    #
    @13
    @14
    @24
    wcel
    #
    wi
    #
    vx
    @24
    cpw
    #
    wral
    #
    @30
    @26
    @27
    @32
    @36
    w3a
    #
    @30
    @25
    @26
    @37
    wa
    #
    @30
    @29
    @2
    @25
    @3
    @29
    simpr
    @0
    @2
    @29
    simplr
    @24
    cA
    @1
    elelpwi
    syl2anc
    #
    @24
    cvv
    wcel
    @25
    @38
    wb
    vs
    vex
    vx
    @24
    cO
    issiga
    ax-mp
    sylib
    simprd
    #
    simp1d
    ralrimiva
    @3
    cO
    cvv
    wcel
    #
    @8
    @28
    wb
    @3
    @25
    vs
    wex
    #
    @41
    @3
    @29
    vs
    wex
    #
    @42
    @0
    @43
    @2
    @0
    @43
    vs
    cA
    n0
    biimpi
    adantr
    @3
    @29
    @25
    vs
    @3
    @29
    @25
    @39
    ex
    eximdv
    mpd
    @25
    @41
    vs
    @24
    cO
    csiga
    elfvex
    exlimiv
    syl
    #
    vs
    cO
    cA
    cvv
    elintg
    syl
    mpbird
    @3
    @11
    vx
    @4
    @3
    @9
    @4
    wcel
    #
    wa
    #
    @11
    @31
    vs
    cA
    wral
    #
    @46
    @31
    vs
    cA
    @46
    @29
    wa
    #
    @30
    @9
    @24
    wcel
    #
    @31
    @48
    @3
    @29
    @3
    @45
    @29
    simpll
    @46
    @29
    simpr
    jca
    @45
    @29
    @49
    @3
    @45
    @29
    @49
    @9
    cA
    @24
    elinti
    imp
    adantll
    @30
    @31
    vx
    @24
    @30
    @27
    @32
    @36
    @40
    simp2d
    r19.21bi
    syl2anc
    ralrimiva
    @46
    @10
    cvv
    wcel
    #
    @11
    @47
    wb
    @3
    @50
    @45
    @3
    @41
    @50
    @44
    cO
    @9
    cvv
    difexg
    syl
    adantr
    vs
    @10
    cA
    cvv
    elintg
    syl
    mpbird
    ralrimiva
    @3
    @16
    vx
    @17
    @3
    @9
    @17
    wcel
    #
    wa
    #
    @13
    @15
    @52
    @13
    wa
    #
    @15
    @33
    vs
    cA
    wral
    #
    @53
    @33
    vs
    cA
    @53
    @29
    wa
    #
    @30
    @9
    @35
    wcel
    #
    wa
    @13
    @33
    @55
    @30
    @56
    @55
    @3
    @29
    @3
    @51
    @13
    @29
    simplll
    @53
    @29
    simpr
    jca
    @53
    @29
    @51
    @56
    @3
    @51
    @13
    @29
    simpllr
    @51
    @29
    wa
    @9
    @24
    wss
    @56
    @51
    @29
    @9
    @4
    @24
    @9
    @4
    elpwi
    @24
    cA
    intss1
    sylan9ss
    vx
    @24
    selpw
    sylibr
    sylancom
    jca
    @52
    @13
    @29
    simplr
    @30
    @34
    vx
    @35
    @30
    @27
    @32
    @36
    @40
    simp3d
    r19.21bi
    sylc
    ralrimiva
    @53
    @14
    cvv
    wcel
    #
    @15
    @54
    wb
    @51
    @57
    @3
    @13
    @9
    @17
    uniexg
    ad2antlr
    vs
    @14
    cA
    cvv
    elintg
    syl
    mpbird
    ex
    ralrimiva
    3jca
    @5
    @20
    @7
    @19
    wa
    vx
    @4
    cO
    issiga
    biimpar
    syl12anc
end
