include "cr.mm"
include "wss.mm"
include "c1o.mm"
include "crrn.mm"
include "cfv.mm"
include "c0.mm"
include "csn.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt.mm"
include "cima.mm"
include "cres.mm"
include "cmopn.mm"
include "ccmp.mm"
include "wcel.mm"
include "ccld.mm"
include "cbnd.mm"
include "wa.mm"
include "cfn.mm"
include "cmap.mm"
include "co.mm"
include "wb.mm"
include "df1o2.mm"
include "snfi.mm"
include "eqeltri.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wf.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "wceq.mm"
include "wral.mm"
include "cismty.mm"
include "cvv.mm"
include "0ex.mm"
include "eqid.mm"
include "ismrer1.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "eleqtrri.mm"
include "cxmt.mm"
include "rexmet.mm"
include "cme.mm"
include "rrnmet.mm"
include "metxmet.mm"
include "mp2b.mm"
include "isismty.mm"
include "mp2an.mm"
include "mpbi.mm"
include "simpli.mm"
include "f1of.mm"
include "frn.mm"
include "sstri.mm"
include "a1i.mm"
include "rrnheibor.mm"
include "sylancr.mm"
include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "cc.mm"
include "cnxmet.mm"
include "id.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "xmetres2.mm"
include "syl5eqel.mm"
include "ismtyhmeo.mm"
include "syl2anc.mm"
include "ismtyres.mm"
include "syl22anc.mm"
include "xpss12.mm"
include "anidms.mm"
include "resabs1d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "sseldd.mm"
include "hmphi.mm"
include "syl.mm"
include "cmphmph.mm"
include "wi.mm"
include "hmphsym.mm"
include "impbid.mm"
include "cioo.mm"
include "ctg.mm"
include "tgioo.mm"
include "eqtri.mm"
include "sselii.mm"
include "ctopon.mm"
include "retopon.mm"
include "toponunii.mm"
include "hmeocld.mm"
include "ismtybnd.mm"
include "syl3anc.mm"
include "anbi12d.mm"
include "3bitr4d.mm"

theorem reheibor
  let cT: class T
  let cU: class U
  let cM: class M
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume reheibor.2: |- M = ( ( abs o. - ) |` ( Y X. Y ) )
  assume reheibor.3: |- T = ( MetOpen ` M )
  assume reheibor.4: |- U = ( topGen ` ran (,) )


  assert |- ( Y C_ RR -> ( T e. Comp <-> ( Y e. ( Clsd ` U ) /\ M e. ( Bnd ` Y ) ) ) )

  proof
    cY
    cr
    wss
    #
    c1o
    crrn
    cfv
    #
    vx
    cr
    c0
    csn
    #
    vx
    cv
    csn
    cxp
    cmpt
    #
    cY
    cima
    #
    @4
    cxp
    cres
    #
    cmopn
    cfv
    #
    ccmp
    wcel
    #
    @4
    @1
    cmopn
    cfv
    #
    ccld
    cfv
    wcel
    #
    @5
    @4
    cbnd
    cfv
    wcel
    #
    wa
    #
    cT
    ccmp
    wcel
    #
    cY
    cU
    ccld
    cfv
    wcel
    #
    cM
    cY
    cbnd
    cfv
    wcel
    #
    wa
    @0
    c1o
    cfn
    wcel
    #
    @4
    cr
    c1o
    cmap
    co
    #
    wss
    #
    @7
    @11
    wb
    c1o
    @2
    cfn
    df1o2
    c0
    snfi
    eqeltri
    #
    @17
    @0
    @4
    @3
    crn
    #
    @16
    @3
    cY
    imassrn
    cr
    @16
    @3
    wf1o
    #
    cr
    @16
    @3
    wf
    @19
    @16
    wss
    @20
    vy
    cv
    #
    vz
    cv
    #
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    #
    cres
    #
    co
    @21
    @3
    cfv
    @22
    @3
    cfv
    @1
    co
    wceq
    vz
    cr
    wral
    vy
    cr
    wral
    #
    @3
    @25
    @1
    cismty
    co
    #
    wcel
    #
    @20
    @26
    wa
    #
    @3
    @25
    @2
    crrn
    cfv
    #
    cismty
    co
    #
    @27
    c0
    cvv
    wcel
    @3
    @31
    wcel
    0ex
    vx
    c0
    @25
    @3
    cvv
    @25
    eqid
    #
    @3
    eqid
    ismrer1
    ax-mp
    @1
    @30
    @25
    cismty
    c1o
    @2
    crrn
    df1o2
    fveq2i
    oveq2i
    eleqtrri
    #
    @25
    cr
    cxmt
    cfv
    wcel
    #
    @1
    @16
    cxmt
    cfv
    wcel
    #
    @28
    @29
    wb
    @25
    @32
    rexmet
    #
    @15
    @1
    @16
    cme
    cfv
    wcel
    @35
    @18
    c1o
    @16
    @16
    eqid
    #
    rrnmet
    @1
    @16
    metxmet
    mp2b
    #
    vy
    vz
    @3
    @25
    @1
    cr
    @16
    isismty
    mp2an
    mpbi
    simpli
    cr
    @16
    @3
    f1of
    cr
    @16
    @3
    frn
    mp2b
    sstri
    a1i
    #
    @6
    @8
    c1o
    @5
    @16
    @4
    @37
    @5
    eqid
    #
    @6
    eqid
    #
    @8
    eqid
    #
    rrnheibor
    sylancr
    @0
    cT
    @6
    chmph
    wbr
    #
    @12
    @7
    wb
    @0
    @3
    cY
    cres
    #
    cT
    @6
    chmeo
    co
    #
    wcel
    @43
    @0
    cM
    @5
    cismty
    co
    #
    @45
    @44
    @0
    cM
    cY
    cxmt
    cfv
    #
    wcel
    #
    @5
    @4
    cxmt
    cfv
    wcel
    #
    @46
    @45
    wss
    @0
    cM
    @23
    cY
    cY
    cxp
    #
    cres
    #
    @47
    reheibor.2
    @0
    @23
    cc
    cxmt
    cfv
    wcel
    cY
    cc
    wss
    @51
    @47
    wcel
    cnxmet
    @0
    cY
    cr
    cc
    @0
    id
    #
    ax-resscn
    syl6ss
    @23
    cY
    cc
    xmetres2
    sylancr
    syl5eqel
    #
    @0
    @35
    @17
    @49
    @38
    @39
    @1
    @4
    @16
    xmetres2
    sylancr
    #
    cT
    @6
    cM
    @5
    cY
    @4
    reheibor.3
    @41
    ismtyhmeo
    syl2anc
    @0
    @44
    @25
    @50
    cres
    #
    @5
    cismty
    co
    #
    @46
    @0
    @34
    @35
    @28
    @0
    @44
    @56
    wcel
    @34
    @0
    @36
    a1i
    @35
    @0
    @38
    a1i
    @28
    @0
    @33
    a1i
    @52
    cY
    @4
    @55
    @5
    @3
    @25
    @1
    cr
    @16
    @4
    eqid
    @55
    eqid
    @40
    ismtyres
    syl22anc
    @0
    @55
    cM
    @5
    cismty
    @0
    @55
    @51
    cM
    @0
    @23
    @50
    @24
    @0
    @50
    @24
    wss
    cY
    cr
    cY
    cr
    xpss12
    anidms
    resabs1d
    reheibor.2
    syl6eqr
    oveq1d
    eleqtrd
    #
    sseldd
    @44
    cT
    @6
    hmphi
    syl
    @43
    @12
    @7
    cT
    @6
    cmphmph
    @43
    @6
    cT
    chmph
    wbr
    @7
    @12
    wi
    cT
    @6
    hmphsym
    @6
    cT
    cmphmph
    syl
    impbid
    syl
    @0
    @13
    @9
    @14
    @10
    @0
    @3
    cU
    @8
    chmeo
    co
    #
    wcel
    @0
    @13
    @9
    wb
    @27
    @58
    @3
    @34
    @35
    @27
    @58
    wss
    @36
    @38
    cU
    @8
    @25
    @1
    cr
    @16
    cU
    cioo
    crn
    ctg
    cfv
    #
    @25
    cmopn
    cfv
    #
    reheibor.4
    @25
    @60
    @32
    @60
    eqid
    tgioo
    eqtri
    @42
    ismtyhmeo
    mp2an
    @33
    sselii
    @52
    cY
    @3
    cU
    @8
    cr
    cr
    cU
    cU
    @59
    cr
    ctopon
    cfv
    reheibor.4
    retopon
    eqeltri
    toponunii
    hmeocld
    sylancr
    @0
    @48
    @49
    @44
    @46
    wcel
    @14
    @10
    wb
    @53
    @54
    @57
    @44
    cM
    @5
    cY
    @4
    ismtybnd
    syl3anc
    anbi12d
    3bitr4d
end
