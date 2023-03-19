include "cico.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "cmpt2.mm"
include "df-ico.mm"
include "reseq1i.mm"
include "wss.mm"
include "wceq.mm"
include "ressxr.mm"
include "resmpt2.mm"
include "mp2an.mm"
include "eqtri.mm"
include "wcel.mm"
include "nfv.mm"
include "nfrab1.mm"
include "rabid.mm"
include "cmnf.mm"
include "wn.mm"
include "cpnf.mm"
include "wo.mm"
include "rexr.mm"
include "nltmnf.mm"
include "syl.mm"
include "renemnf.mm"
include "neneqd.mm"
include "jca.mm"
include "pm4.56.mm"
include "sylib.mm"
include "wb.mm"
include "mnfxr.mm"
include "xrleloe.mm"
include "sylancl.mm"
include "mtbird.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "con2d.mm"
include "wi.mm"
include "pnfnlt.mm"
include "breq1.mm"
include "im2anan9.mm"
include "anim2d.mm"
include "renepnf.mm"
include "pm4.71i.mm"
include "wne.mm"
include "xrnemnf.mm"
include "anbi1i.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "pm5.61.mm"
include "3bitr3i.mm"
include "anass.mm"
include "3bitr2ri.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "simprbi.mm"
include "a1i.mm"
include "jcad.mm"
include "syl6ibr.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "sseli.mm"
include "impbid1.mm"
include "eqrd.mm"
include "mpt2eq3ia.mm"
include "3eqtri.mm"

theorem icorempt2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assume icorempt2.1: |- F = ( [,) |` ( RR X. RR ) )

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- F = ( x e. RR , y e. RR |-> { z e. RR | ( x <_ z /\ z < y ) } )

  proof
    cF
    cico
    cr
    cr
    cxp
    #
    cres
    #
    vx
    vy
    cr
    cr
    vx
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @3
    vy
    cv
    #
    clt
    wbr
    #
    wa
    #
    vz
    cxr
    crab
    #
    cmpt2
    #
    vx
    vy
    cr
    cr
    @7
    vz
    cr
    crab
    #
    cmpt2
    icorempt2.1
    @1
    vx
    vy
    cxr
    cxr
    @8
    cmpt2
    #
    @0
    cres
    #
    @9
    cico
    @11
    @0
    vx
    vy
    vz
    df-ico
    reseq1i
    cr
    cxr
    wss
    #
    @13
    @12
    @9
    wceq
    ressxr
    ressxr
    vx
    vy
    cxr
    cxr
    cr
    cr
    @8
    resmpt2
    mp2an
    eqtri
    vx
    vy
    cr
    cr
    @8
    @10
    @2
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    wa
    #
    vz
    @8
    @10
    @16
    vz
    nfv
    @7
    vz
    cxr
    nfrab1
    @7
    vz
    cr
    nfrab1
    @16
    @3
    @8
    wcel
    #
    @3
    @10
    wcel
    #
    @16
    @17
    @3
    cr
    wcel
    #
    @7
    wa
    @18
    @16
    @17
    @19
    @7
    @17
    @3
    cxr
    wcel
    #
    @7
    wa
    #
    @16
    @19
    @7
    vz
    cxr
    rabid
    #
    @16
    @21
    @20
    @3
    cmnf
    wceq
    #
    wn
    #
    @3
    cpnf
    wceq
    #
    wn
    #
    wa
    #
    wa
    #
    @19
    @16
    @7
    @27
    @20
    @14
    @4
    @24
    @15
    @6
    @26
    @14
    @23
    @4
    @14
    @4
    wn
    @23
    @2
    cmnf
    cle
    wbr
    #
    wn
    @14
    @29
    @2
    cmnf
    clt
    wbr
    #
    @2
    cmnf
    wceq
    #
    wo
    #
    @14
    @30
    wn
    #
    @31
    wn
    #
    wa
    @32
    wn
    @14
    @33
    @34
    @14
    @2
    cxr
    wcel
    #
    @33
    @2
    rexr
    #
    @2
    nltmnf
    syl
    @14
    @2
    cmnf
    @2
    renemnf
    neneqd
    jca
    @30
    @31
    pm4.56
    sylib
    @14
    @35
    cmnf
    cxr
    wcel
    @29
    @32
    wb
    @36
    mnfxr
    @2
    cmnf
    xrleloe
    sylancl
    mtbird
    @23
    @4
    @29
    @3
    cmnf
    @2
    cle
    breq2
    notbid
    syl5ibrcom
    con2d
    @15
    @5
    cxr
    wcel
    #
    @6
    @26
    wi
    @5
    rexr
    @37
    @25
    @6
    @37
    @6
    wn
    @25
    cpnf
    @5
    clt
    wbr
    #
    wn
    @5
    pnfnlt
    @25
    @6
    @38
    @3
    cpnf
    @5
    clt
    breq1
    notbid
    syl5ibrcom
    con2d
    syl
    im2anan9
    anim2d
    @19
    @19
    @26
    wa
    #
    @20
    @24
    wa
    #
    @26
    wa
    #
    @28
    @19
    @26
    @19
    @3
    cpnf
    @3
    renepnf
    neneqd
    pm4.71i
    @20
    @3
    cmnf
    wne
    #
    wa
    #
    @26
    wa
    @19
    @25
    wo
    #
    @26
    wa
    @41
    @39
    @43
    @44
    @26
    @3
    xrnemnf
    anbi1i
    @43
    @40
    @26
    @42
    @24
    @20
    @3
    cmnf
    df-ne
    anbi2i
    anbi1i
    @19
    @25
    pm5.61
    3bitr3i
    @20
    @24
    @26
    anass
    3bitr2ri
    syl6ib
    syl5bi
    @17
    @7
    wi
    @16
    @17
    @20
    @7
    @22
    simprbi
    a1i
    jcad
    @7
    vz
    cr
    rabid
    syl6ibr
    @10
    @8
    @3
    @13
    @10
    @8
    wss
    ressxr
    @7
    vz
    cr
    cxr
    rabss2
    ax-mp
    sseli
    impbid1
    eqrd
    mpt2eq3ia
    3eqtri
end
