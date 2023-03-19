include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cen.mm"
include "wa.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "brdomi.mm"
include "adantr.mm"
include "c0.mm"
include "cfv.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wf.mm"
include "f1f.mm"
include "adantl.mm"
include "peano1.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "difsnen.mm"
include "syl3anc.mm"
include "crn.mm"
include "cun.mm"
include "cin.mm"
include "wceq.mm"
include "wf1o.mm"
include "vex.mm"
include "f1f1orn.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "ensymd.mm"
include "brrelexi.mm"
include "limom.mm"
include "limenpsi.mm"
include "syl.mm"
include "cima.mm"
include "cres.mm"
include "resex.mm"
include "wss.mm"
include "simpr.mm"
include "difss.mm"
include "f1ores.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfn.mm"
include "f1orn.mm"
include "simprbi.mm"
include "imadif.mm"
include "3syl.mm"
include "f1fn.mm"
include "fnima.mm"
include "fnsnfv.mm"
include "eqcomd.mm"
include "difeq12d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "entr.mm"
include "syl2anc.mm"
include "difexg.mm"
include "enrefg.mm"
include "disjdif.mm"
include "a1i.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "sseq0.mm"
include "mp2an.mm"
include "unen.mm"
include "syl22anc.mm"
include "frn.mm"
include "undif.mm"
include "sylib.mm"
include "uncom.mm"
include "wn.mm"
include "eldifn.mm"
include "fnfvelrn.mm"
include "nsyl3.mm"
include "disjsn.mm"
include "sylibr.mm"
include "undif4.mm"
include "syl5eq.mm"
include "difeq1d.mm"
include "3brtr3d.mm"
include "exlimddv.mm"
include "difsn.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"

theorem infdifsn
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( _om ~<_ A -> ( A \ { B } ) ~~ A )

  proof
    com
    cA
    cdom
    wbr
    #
    cB
    cA
    wcel
    #
    cA
    cB
    csn
    cdif
    #
    cA
    cen
    wbr
    #
    @0
    @1
    wa
    #
    com
    cA
    vf
    cv
    #
    wf1
    #
    @3
    vf
    @0
    @6
    vf
    wex
    @1
    com
    cA
    vf
    brdomi
    adantr
    @4
    @6
    wa
    #
    @2
    cA
    c0
    @5
    cfv
    #
    csn
    #
    cdif
    #
    cen
    wbr
    #
    @10
    cA
    cen
    wbr
    @3
    @7
    cA
    cvv
    wcel
    #
    @1
    @8
    cA
    wcel
    #
    @11
    @0
    @12
    @1
    @6
    com
    cA
    cdom
    reldom
    brrelex2i
    #
    ad2antrr
    #
    @0
    @1
    @6
    simplr
    @7
    com
    cA
    @5
    wf
    #
    c0
    com
    wcel
    #
    @13
    @6
    @16
    @4
    com
    cA
    @5
    f1f
    adantl
    #
    peano1
    com
    cA
    c0
    @5
    ffvelrn
    sylancl
    cB
    @8
    cvv
    cA
    difsnen
    syl3anc
    @7
    cA
    @10
    @7
    @5
    crn
    #
    cA
    @19
    cdif
    #
    cun
    #
    @19
    @9
    cdif
    #
    @20
    cun
    #
    cA
    @10
    cen
    @7
    @19
    @22
    cen
    wbr
    #
    @20
    @20
    cen
    wbr
    #
    @19
    @20
    cin
    #
    c0
    wceq
    #
    @22
    @20
    cin
    #
    c0
    wceq
    #
    @21
    @23
    cen
    wbr
    @7
    @19
    com
    cen
    wbr
    com
    @22
    cen
    wbr
    #
    @24
    @7
    com
    @19
    @7
    @5
    cvv
    wcel
    com
    @19
    @5
    wf1o
    #
    com
    @19
    cen
    wbr
    vf
    vex
    #
    @6
    @31
    @4
    com
    cA
    @5
    f1f1orn
    adantl
    #
    com
    @19
    @5
    cvv
    f1oen3g
    sylancr
    ensymd
    @7
    com
    com
    c0
    csn
    #
    cdif
    #
    cen
    wbr
    #
    @35
    @22
    cen
    wbr
    @30
    @7
    com
    cvv
    wcel
    #
    @36
    @0
    @37
    @1
    @6
    com
    cA
    cdom
    reldom
    brrelexi
    ad2antrr
    com
    cvv
    limom
    limenpsi
    syl
    @7
    @35
    @5
    @35
    cima
    #
    @22
    cen
    @7
    @5
    @35
    cres
    #
    cvv
    wcel
    @35
    @38
    @39
    wf1o
    #
    @35
    @38
    cen
    wbr
    @5
    @35
    @32
    resex
    @7
    @6
    @35
    com
    wss
    @40
    @4
    @6
    simpr
    com
    @34
    difss
    com
    cA
    @35
    @5
    f1ores
    sylancl
    @35
    @38
    @39
    cvv
    f1oen3g
    sylancr
    @7
    @38
    @5
    com
    cima
    #
    @5
    @34
    cima
    #
    cdif
    #
    @22
    @7
    @31
    @5
    ccnv
    wfun
    #
    @38
    @43
    wceq
    @33
    @31
    @5
    com
    wfn
    #
    @44
    com
    @5
    f1orn
    simprbi
    com
    @34
    @5
    imadif
    3syl
    @7
    @41
    @19
    @42
    @9
    @7
    @45
    @41
    @19
    wceq
    @6
    @45
    @4
    com
    cA
    @5
    f1fn
    adantl
    #
    com
    @5
    fnima
    syl
    @7
    @9
    @42
    @7
    @45
    @17
    @9
    @42
    wceq
    @46
    peano1
    com
    c0
    @5
    fnsnfv
    sylancl
    eqcomd
    difeq12d
    eqtrd
    breqtrd
    com
    @35
    @22
    entr
    syl2anc
    @19
    com
    @22
    entr
    syl2anc
    @7
    @12
    @20
    cvv
    wcel
    @25
    @15
    cA
    @19
    cvv
    difexg
    @20
    cvv
    enrefg
    3syl
    @27
    @7
    @19
    cA
    disjdif
    #
    a1i
    @29
    @7
    @28
    @26
    wss
    #
    @27
    @29
    @22
    @19
    wss
    @48
    @19
    @9
    difss
    @22
    @19
    @20
    ssrin
    ax-mp
    @47
    @28
    @26
    sseq0
    mp2an
    a1i
    @19
    @22
    @20
    @20
    unen
    syl22anc
    @7
    @19
    cA
    wss
    #
    @21
    cA
    wceq
    @7
    @16
    @49
    @18
    com
    cA
    @5
    frn
    syl
    @19
    cA
    undif
    sylib
    #
    @7
    @23
    @20
    @22
    cun
    #
    @10
    @22
    @20
    uncom
    @7
    @51
    @20
    @19
    cun
    #
    @9
    cdif
    #
    @10
    @7
    @20
    @9
    cin
    c0
    wceq
    #
    @51
    @53
    wceq
    @7
    @8
    @20
    wcel
    #
    wn
    @54
    @55
    @8
    @19
    wcel
    #
    @7
    @8
    cA
    @19
    eldifn
    @7
    @45
    @17
    @56
    @46
    peano1
    com
    c0
    @5
    fnfvelrn
    sylancl
    nsyl3
    @20
    @8
    disjsn
    sylibr
    @20
    @19
    @9
    undif4
    syl
    @7
    @52
    cA
    @9
    @7
    @52
    @21
    cA
    @20
    @19
    uncom
    @50
    syl5eq
    difeq1d
    eqtrd
    syl5eq
    3brtr3d
    ensymd
    @2
    @10
    cA
    entr
    syl2anc
    exlimddv
    @0
    @1
    wn
    #
    wa
    @2
    cA
    cA
    cen
    @57
    @2
    cA
    wceq
    @0
    cB
    cA
    difsn
    adantl
    @0
    cA
    cA
    cen
    wbr
    #
    @57
    @0
    @12
    @58
    @14
    cA
    cvv
    enrefg
    syl
    adantr
    eqbrtrd
    pm2.61dan
end
