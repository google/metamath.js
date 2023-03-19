include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "wfun.mm"
include "crn.mm"
include "wnel.mm"
include "wa.mm"
include "cdm.mm"
include "cixp.mm"
include "dfac3.mm"
include "vex.mm"
include "rnex.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "spcv.mm"
include "cmpt.mm"
include "wn.mm"
include "df-nel.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "fvelrn.mm"
include "adantlr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "simpll.mm"
include "sylan.mm"
include "simplr.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "dmex.mm"
include "mptelixpg.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ne0i.mm"
include "syl.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5com.mm"
include "alrimiv.mm"
include "csn.mm"
include "cdif.mm"
include "cid.mm"
include "cres.mm"
include "wfn.mm"
include "fnresi.mm"
include "fnfun.mm"
include "neldifsn.mm"
include "difexg.mm"
include "resiexg.mm"
include "funeq.mm"
include "rneq.mm"
include "rnresi.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "notbid.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "dmeq.mm"
include "dmresi.mm"
include "ixpeq1d.mm"
include "fveq1.mm"
include "fvresi.mm"
include "sylan9eq.mm"
include "ixpeq2dva.mm"
include "eqtrd.mm"
include "neeq1d.mm"
include "mp2ani.mm"
include "n0.mm"
include "elixp.mm"
include "eldifsn.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"
include "cbvralv.mm"
include "adantl.mm"
include "sylbi.mm"
include "eximi.mm"
include "impbii.mm"

theorem dfac9
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let vt: setvar t

  disjoint f x
  disjoint f g
  disjoint f s
  disjoint f t
  disjoint g s
  disjoint g t
  disjoint g x
  disjoint s t
  disjoint s x
  disjoint t x
  assert |- ( CHOICE <-> A. f ( ( Fun f /\ (/) e/ ran f ) -> X_ x e. dom f ( f ` x ) =/= (/) ) )

  proof
    wac
    vt
    cv
    #
    c0
    wne
    #
    @0
    vg
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vt
    vs
    cv
    #
    wral
    #
    vg
    wex
    #
    vs
    wal
    #
    vf
    cv
    #
    wfun
    #
    c0
    @10
    crn
    #
    wnel
    #
    wa
    #
    vx
    @10
    cdm
    #
    vx
    cv
    #
    @10
    cfv
    #
    cixp
    #
    c0
    wne
    #
    wi
    #
    vf
    wal
    #
    vs
    vt
    vg
    dfac3
    @9
    @21
    @9
    @20
    vf
    @9
    @5
    vt
    @12
    wral
    #
    vg
    wex
    #
    @14
    @19
    @8
    @23
    vs
    @12
    @10
    vf
    vex
    #
    rnex
    @6
    @12
    wceq
    @7
    @22
    vg
    @5
    vt
    @6
    @12
    raleq
    exbidv
    spcv
    @14
    @22
    @19
    vg
    @14
    @22
    @19
    @14
    @22
    wa
    #
    vx
    @15
    @17
    @2
    cfv
    #
    cmpt
    #
    @18
    wcel
    #
    @19
    @25
    @26
    @17
    wcel
    #
    vx
    @15
    wral
    #
    @28
    @25
    @29
    vx
    @15
    @25
    @16
    @15
    wcel
    #
    wa
    #
    @17
    c0
    wne
    #
    @29
    @14
    @31
    @33
    @22
    @14
    @31
    wa
    #
    c0
    @12
    wcel
    #
    wn
    #
    @33
    @13
    @36
    @11
    @31
    @13
    @36
    c0
    @12
    df-nel
    #
    biimpi
    ad2antlr
    @34
    @35
    @17
    c0
    @34
    @17
    @12
    wcel
    #
    @17
    c0
    wceq
    @35
    @11
    @31
    @38
    @13
    @16
    @10
    fvelrn
    #
    adantlr
    @17
    c0
    @12
    eleq1
    syl5ibcom
    necon3bd
    mpd
    adantlr
    @32
    @38
    @22
    @33
    @29
    wi
    #
    @25
    @11
    @31
    @38
    @11
    @13
    @22
    simpll
    @39
    sylan
    @14
    @22
    @31
    simplr
    @5
    @40
    vt
    @17
    @12
    @0
    @17
    wceq
    #
    @1
    @33
    @4
    @29
    @0
    @17
    c0
    neeq1
    @41
    @3
    @26
    @0
    @17
    @0
    @17
    @2
    fveq2
    @41
    id
    eleq12d
    imbi12d
    rspcva
    syl2anc
    mpd
    ralrimiva
    @15
    cvv
    wcel
    @28
    @30
    wb
    @10
    @24
    dmex
    vx
    @15
    @26
    @17
    cvv
    mptelixpg
    ax-mp
    sylibr
    @18
    @27
    ne0i
    syl
    ex
    exlimdv
    syl5com
    alrimiv
    @21
    @8
    vs
    @21
    vx
    @6
    c0
    csn
    #
    cdif
    #
    @16
    cixp
    #
    c0
    wne
    #
    @8
    @21
    cid
    @43
    cres
    #
    wfun
    #
    c0
    @43
    wcel
    #
    wn
    #
    @45
    @46
    @43
    wfn
    @47
    @43
    fnresi
    @43
    @46
    fnfun
    ax-mp
    c0
    @6
    neldifsn
    @20
    @47
    @49
    wa
    #
    @45
    wi
    vf
    @46
    @43
    cvv
    wcel
    #
    @46
    cvv
    wcel
    @6
    cvv
    wcel
    @51
    vs
    vex
    @6
    @42
    cvv
    difexg
    ax-mp
    @43
    cvv
    resiexg
    ax-mp
    @10
    @46
    wceq
    #
    @14
    @50
    @19
    @45
    @52
    @11
    @47
    @13
    @49
    @10
    @46
    funeq
    @13
    @36
    @52
    @49
    @37
    @52
    @35
    @48
    @52
    @12
    @43
    c0
    @52
    @12
    @46
    crn
    @43
    @10
    @46
    rneq
    @43
    rnresi
    syl6eq
    eleq2d
    notbid
    syl5bb
    anbi12d
    @52
    @18
    @44
    c0
    @52
    @18
    vx
    @43
    @17
    cixp
    @44
    @52
    vx
    @15
    @43
    @17
    @52
    @15
    @46
    cdm
    @43
    @10
    @46
    dmeq
    @43
    dmresi
    syl6eq
    ixpeq1d
    @52
    vx
    @43
    @17
    @16
    @52
    @16
    @43
    wcel
    #
    @17
    @16
    @46
    cfv
    @16
    @16
    @10
    @46
    fveq1
    @43
    @16
    fvresi
    sylan9eq
    ixpeq2dva
    eqtrd
    neeq1d
    imbi12d
    spcv
    mp2ani
    @45
    @2
    @44
    wcel
    #
    vg
    wex
    @8
    vg
    @44
    n0
    @54
    @7
    vg
    @54
    @2
    @43
    wfn
    #
    @16
    @2
    cfv
    #
    @16
    wcel
    #
    vx
    @43
    wral
    #
    wa
    @7
    vx
    @43
    @16
    @2
    vg
    vex
    elixp
    @58
    @7
    @55
    @58
    @7
    @58
    @16
    c0
    wne
    #
    @57
    wi
    #
    vx
    @6
    wral
    @7
    @57
    @60
    vx
    @43
    @6
    @53
    @57
    wi
    @16
    @6
    wcel
    #
    @59
    wa
    #
    @57
    wi
    @61
    @60
    wi
    @53
    @62
    @57
    @16
    @6
    c0
    eldifsn
    imbi1i
    @61
    @59
    @57
    impexp
    bitri
    ralbii2
    @60
    @5
    vx
    vt
    @6
    @16
    @0
    wceq
    #
    @59
    @1
    @57
    @4
    @16
    @0
    c0
    neeq1
    @63
    @56
    @3
    @16
    @0
    @16
    @0
    @2
    fveq2
    @63
    id
    eleq12d
    imbi12d
    cbvralv
    bitri
    biimpi
    adantl
    sylbi
    eximi
    sylbi
    syl
    alrimiv
    impbii
    bitri
end
