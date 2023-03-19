include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "ciun.mm"
include "cid.mm"
include "wcel.mm"
include "wrex.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elxp.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "exbii.mm"
include "3bitri.mm"
include "eliun.mm"
include "wne.mm"
include "wn.mm"
include "eldif.mm"
include "opelxp.mm"
include "wbr.mm"
include "df-br.mm"
include "vex.mm"
include "ideq.mm"
include "bitr3i.mm"
include "necon3bbii.mm"
include "anbi12i.mm"
include "bitri.mm"
include "anbi2i.mm"
include "2exbii.mm"
include "eldifi.mm"
include "elxpi.mm"
include "simpl.mm"
include "2eximi.mm"
include "3syl.mm"
include "ancli.mm"
include "19.42vv.mm"
include "sylibr.mm"
include "ancom.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "2exbidv.mm"
include "mpbid.mm"
include "biimpar.mm"
include "exlimivv.mm"
include "impbii.mm"
include "r19.42v.mm"
include "simprl.mm"
include "velsn.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "simprr.mm"
include "eldifad.mm"
include "eldifbd.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "jca31.mm"
include "adantll.mm"
include "sneq.mm"
include "eleq2d.mm"
include "difeq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "biimpi.mm"
include "r19.29a.mm"
include "simpll.mm"
include "vsnid.mm"
include "a1i.mm"
include "simplr.mm"
include "simpr.mm"
include "eldifd.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem xpdifid
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A i
  disjoint A j
  disjoint A p
  disjoint A y
  disjoint i j
  disjoint i p
  disjoint i x
  disjoint i y
  disjoint j p
  disjoint j x
  disjoint j y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint B i
  disjoint B j
  disjoint B p
  disjoint B y
  assert |- U_ x e. A ( { x } X. ( B \ { x } ) ) = ( ( A X. B ) \ _I )

  proof
    vp
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    @1
    cdif
    #
    cxp
    #
    ciun
    #
    cA
    cB
    cxp
    #
    cid
    cdif
    #
    vp
    cv
    #
    @3
    wcel
    #
    vx
    cA
    wrex
    #
    @7
    vi
    cv
    #
    vj
    cv
    #
    cop
    #
    wceq
    #
    @10
    @1
    wcel
    #
    @11
    @2
    wcel
    #
    wa
    #
    wa
    #
    vx
    cA
    wrex
    #
    vj
    wex
    #
    vi
    wex
    #
    @7
    @4
    wcel
    @7
    @6
    wcel
    #
    @9
    @17
    vj
    wex
    #
    vi
    wex
    #
    vx
    cA
    wrex
    @22
    vx
    cA
    wrex
    #
    vi
    wex
    @20
    @8
    @23
    vx
    cA
    vi
    vj
    @7
    @1
    @2
    elxp
    rexbii
    @22
    vx
    vi
    cA
    rexcom4
    @24
    @19
    vi
    @17
    vx
    vj
    cA
    rexcom4
    exbii
    3bitri
    vx
    @7
    cA
    @3
    eliun
    @13
    @12
    @6
    wcel
    #
    wa
    #
    vj
    wex
    vi
    wex
    #
    @13
    @10
    cA
    wcel
    #
    @11
    cB
    wcel
    #
    wa
    #
    @10
    @11
    wne
    #
    wa
    #
    wa
    #
    vj
    wex
    vi
    wex
    @21
    @20
    @26
    @33
    vi
    vj
    @25
    @32
    @13
    @25
    @12
    @5
    wcel
    #
    @12
    cid
    wcel
    #
    wn
    #
    wa
    @32
    @12
    @5
    cid
    eldif
    @34
    @30
    @36
    @31
    @10
    @11
    cA
    cB
    opelxp
    @35
    @10
    @11
    @35
    @10
    @11
    cid
    wbr
    @10
    @11
    wceq
    @10
    @11
    cid
    df-br
    @10
    @11
    vj
    vex
    ideq
    bitr3i
    necon3bbii
    anbi12i
    bitri
    anbi2i
    2exbii
    @21
    @27
    @21
    @21
    @13
    wa
    #
    vj
    wex
    vi
    wex
    #
    @27
    @21
    @21
    @13
    vj
    wex
    vi
    wex
    #
    wa
    @38
    @21
    @39
    @21
    @7
    @5
    wcel
    @13
    @30
    wa
    #
    vj
    wex
    vi
    wex
    @39
    @7
    @5
    cid
    eldifi
    vi
    vj
    @7
    cA
    cB
    elxpi
    @40
    @13
    vi
    vj
    @13
    @30
    simpl
    2eximi
    3syl
    ancli
    @21
    @13
    vi
    vj
    19.42vv
    sylibr
    @21
    @37
    @26
    vi
    vj
    @37
    @13
    @21
    wa
    @21
    @26
    @21
    @13
    ancom
    @21
    @13
    @21
    @25
    @13
    @21
    @25
    wb
    @21
    @7
    @12
    @6
    eleq1
    #
    adantl
    pm5.32da
    syl5bb
    2exbidv
    mpbid
    @26
    @21
    vi
    vj
    @13
    @21
    @25
    @41
    biimpar
    exlimivv
    impbii
    @18
    @33
    vi
    vj
    @18
    @13
    @16
    vx
    cA
    wrex
    #
    wa
    @33
    @13
    @16
    vx
    cA
    r19.42v
    @42
    @32
    @13
    @42
    @32
    @42
    @10
    vy
    cv
    #
    csn
    #
    wcel
    #
    @11
    cB
    @44
    cdif
    #
    wcel
    #
    wa
    #
    @32
    vy
    cA
    @43
    cA
    wcel
    #
    @48
    @32
    @42
    @49
    @48
    wa
    #
    @28
    @29
    @31
    @50
    @10
    @43
    cA
    @50
    @45
    @10
    @43
    wceq
    @49
    @45
    @47
    simprl
    vi
    @43
    velsn
    sylib
    #
    @49
    @48
    simpl
    eqeltrd
    @50
    @11
    cB
    @44
    @49
    @45
    @47
    simprr
    #
    eldifad
    @50
    @10
    @43
    @11
    @51
    @50
    @11
    @43
    @50
    @11
    @44
    wcel
    #
    wn
    @11
    @43
    wne
    @50
    @11
    cB
    @44
    @52
    eldifbd
    @53
    @11
    @43
    vj
    @43
    velsn
    necon3bbii
    sylib
    necomd
    eqnetrd
    jca31
    adantll
    @42
    @48
    vy
    cA
    wrex
    @16
    @48
    vx
    vy
    cA
    @0
    @43
    wceq
    #
    @14
    @45
    @15
    @47
    @54
    @1
    @44
    @10
    @0
    @43
    sneq
    #
    eleq2d
    @54
    @2
    @46
    @11
    @54
    @1
    @44
    cB
    @55
    difeq2d
    eleq2d
    anbi12d
    cbvrexv
    biimpi
    r19.29a
    @32
    @28
    @10
    @10
    csn
    #
    wcel
    #
    @11
    cB
    @56
    cdif
    #
    wcel
    #
    @42
    @28
    @29
    @31
    simpll
    @57
    @32
    vi
    vsnid
    a1i
    @32
    @11
    cB
    @56
    @28
    @29
    @31
    simplr
    @32
    @11
    @10
    wne
    @11
    @56
    wcel
    #
    wn
    @32
    @10
    @11
    @30
    @31
    simpr
    necomd
    @60
    @11
    @10
    vj
    @10
    velsn
    necon3bbii
    sylibr
    eldifd
    @16
    @57
    @59
    wa
    vx
    @10
    cA
    @0
    @10
    wceq
    #
    @14
    @57
    @15
    @59
    @61
    @1
    @56
    @10
    @0
    @10
    sneq
    #
    eleq2d
    @61
    @2
    @58
    @11
    @61
    @1
    @56
    cB
    @62
    difeq2d
    eleq2d
    anbi12d
    rspcev
    syl12anc
    impbii
    anbi2i
    bitri
    2exbii
    3bitr4i
    3bitr4i
    eqriv
end
