include "wcel.mm"
include "cop.mm"
include "cdrng.mm"
include "crngo.mm"
include "crn.mm"
include "cgi.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "wa.mm"
include "cvv.mm"
include "wbr.mm"
include "df-br.mm"
include "cv.mm"
include "df-drngo.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "sylbir.mm"
include "anim1i.mm"
include "ancoms.mm"
include "cablo.mm"
include "rngoablo2.mm"
include "elex.mm"
include "syl.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "jca.mm"
include "copab.mm"
include "eleq2i.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "rneq.mm"
include "fveq2.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "anbi12d.mm"
include "opeq2.mm"
include "reseq1.mm"
include "opelopabg.mm"
include "syl5bb.mm"
include "pm5.21nd.mm"

theorem isdivrngo
  let cA: class A
  let cG: class G
  let cH: class H
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y


  assert |- ( H e. A -> ( <. G , H >. e. DivRingOps <-> ( <. G , H >. e. RingOps /\ ( H |` ( ( ran G \ { ( GId ` G ) } ) X. ( ran G \ { ( GId ` G ) } ) ) ) e. GrpOp ) ) )

  proof
    cH
    cA
    wcel
    #
    cG
    cH
    cop
    #
    cdrng
    wcel
    #
    @1
    crngo
    wcel
    #
    cH
    cG
    crn
    #
    cG
    cgi
    cfv
    #
    csn
    #
    cdif
    #
    @7
    cxp
    #
    cres
    #
    cgr
    wcel
    #
    wa
    #
    cG
    cvv
    wcel
    #
    @0
    wa
    #
    @2
    @0
    @13
    @2
    @12
    @0
    @2
    cG
    cH
    cdrng
    wbr
    @12
    cG
    cH
    cdrng
    df-br
    cG
    cH
    cdrng
    vx
    cv
    #
    vy
    cv
    #
    cop
    crngo
    wcel
    @15
    @14
    crn
    @14
    cgi
    cfv
    csn
    cdif
    #
    @16
    cxp
    cres
    cgr
    wcel
    wa
    vx
    vy
    cdrng
    vx
    vy
    df-drngo
    relopabi
    brrelexi
    sylbir
    anim1i
    ancoms
    @0
    @11
    wa
    @12
    @0
    @3
    @12
    @0
    @10
    @3
    cG
    cablo
    wcel
    @12
    cG
    cH
    rngoablo2
    cG
    cablo
    elex
    syl
    ad2antrl
    @0
    @11
    simpl
    jca
    @2
    @1
    vg
    cv
    #
    vh
    cv
    #
    cop
    #
    crngo
    wcel
    #
    @18
    @17
    crn
    #
    @17
    cgi
    cfv
    #
    csn
    #
    cdif
    #
    @24
    cxp
    #
    cres
    #
    cgr
    wcel
    #
    wa
    #
    vg
    vh
    copab
    #
    wcel
    @13
    @11
    cdrng
    @29
    @1
    vg
    vh
    df-drngo
    eleq2i
    @28
    cG
    @18
    cop
    #
    crngo
    wcel
    #
    @18
    @8
    cres
    #
    cgr
    wcel
    #
    wa
    @11
    vg
    vh
    cG
    cH
    cvv
    cA
    @17
    cG
    wceq
    #
    @20
    @31
    @27
    @33
    @34
    @19
    @30
    crngo
    @17
    cG
    @18
    opeq1
    eleq1d
    @34
    @26
    @32
    cgr
    @34
    @25
    @8
    @18
    @34
    @24
    @7
    @34
    @21
    @4
    @23
    @6
    @17
    cG
    rneq
    @34
    @22
    @5
    @17
    cG
    cgi
    fveq2
    sneqd
    difeq12d
    sqxpeqd
    reseq2d
    eleq1d
    anbi12d
    @18
    cH
    wceq
    #
    @31
    @3
    @33
    @10
    @35
    @30
    @1
    crngo
    @18
    cH
    cG
    opeq2
    eleq1d
    @35
    @32
    @9
    cgr
    @18
    cH
    @8
    reseq1
    eleq1d
    anbi12d
    opelopabg
    syl5bb
    pm5.21nd
end
