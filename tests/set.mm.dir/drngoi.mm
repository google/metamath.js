include "cdrng.mm"
include "wcel.mm"
include "crngo.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cv.mm"
include "crn.mm"
include "cgi.mm"
include "copab.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "id.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "anbi12d.mm"
include "opeq2.mm"
include "anbi1d.mm"
include "syl6reqr.mm"
include "reseq1d.mm"
include "anbi2d.mm"
include "bitr4d.mm"
include "elopabi.mm"
include "df-drngo.mm"
include "eleq2s.mm"
include "wrel.mm"
include "relopabi.mm"
include "1st2nd.mm"
include "mpan.mm"
include "mpbird.mm"

theorem drngoi
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  assume drngi.1: |- G = ( 1st ` R )
  assume drngi.2: |- H = ( 2nd ` R )
  assume drngi.3: |- X = ran G
  assume drngi.4: |- Z = ( GId ` G )


  assert |- ( R e. DivRingOps -> ( R e. RingOps /\ ( H |` ( ( X \ { Z } ) X. ( X \ { Z } ) ) ) e. GrpOp ) )

  proof
    cR
    cdrng
    wcel
    #
    cR
    crngo
    wcel
    #
    cH
    cX
    cZ
    csn
    #
    cdif
    #
    @3
    cxp
    #
    cres
    #
    cgr
    wcel
    #
    wa
    cR
    c1st
    cfv
    #
    cR
    c2nd
    cfv
    #
    cop
    #
    crngo
    wcel
    #
    @6
    wa
    #
    @11
    cR
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
    @13
    @12
    crn
    #
    @12
    cgi
    cfv
    #
    csn
    #
    cdif
    #
    @19
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
    cdrng
    @23
    @7
    @13
    cop
    #
    crngo
    wcel
    #
    @13
    @4
    cres
    #
    cgr
    wcel
    #
    wa
    #
    @11
    vg
    vh
    cR
    @12
    @7
    wceq
    #
    @15
    @25
    @22
    @27
    @29
    @14
    @24
    crngo
    @12
    @7
    @13
    opeq1
    eleq1d
    @29
    @21
    @26
    cgr
    @29
    @20
    @4
    @13
    @29
    @19
    @3
    @29
    @16
    cX
    @18
    @2
    @29
    @16
    cG
    crn
    cX
    @29
    @12
    cG
    @29
    @12
    @7
    cG
    @29
    id
    drngi.1
    syl6eqr
    #
    rneqd
    drngi.3
    syl6eqr
    @29
    @17
    cZ
    @29
    @17
    cG
    cgi
    cfv
    cZ
    @29
    @12
    cG
    cgi
    @30
    fveq2d
    drngi.4
    syl6eqr
    sneqd
    difeq12d
    sqxpeqd
    reseq2d
    eleq1d
    anbi12d
    @13
    @8
    wceq
    #
    @28
    @10
    @27
    wa
    @11
    @31
    @25
    @10
    @27
    @31
    @24
    @9
    crngo
    @13
    @8
    @7
    opeq2
    eleq1d
    anbi1d
    @31
    @6
    @27
    @10
    @31
    @5
    @26
    cgr
    @31
    cH
    @13
    @4
    @31
    @13
    @8
    cH
    @31
    id
    drngi.2
    syl6reqr
    reseq1d
    eleq1d
    anbi2d
    bitr4d
    elopabi
    vg
    vh
    df-drngo
    #
    eleq2s
    @0
    @1
    @10
    @6
    @0
    cR
    @9
    crngo
    cdrng
    wrel
    @0
    cR
    @9
    wceq
    @23
    vg
    vh
    cdrng
    @32
    relopabi
    cR
    cdrng
    1st2nd
    mpan
    eleq1d
    anbi1d
    mpbird
end
