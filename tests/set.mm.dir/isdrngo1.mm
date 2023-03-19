include "cdrng.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "crngo.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "wa.mm"
include "wrel.mm"
include "cv.mm"
include "crn.mm"
include "cgi.mm"
include "df-drngo.mm"
include "relopabi.mm"
include "1st2nd.mm"
include "mpan.mm"
include "relrngo.mm"
include "adantr.mm"
include "wb.mm"
include "opeq12i.mm"
include "eqeq2i.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "isdivrngo.mm"
include "ax-mp.mm"
include "sneqi.mm"
include "difeq12i.mm"
include "xpeq12i.mm"
include "reseq2i.mm"
include "eleq1i.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "sylbir.mm"
include "pm5.21nii.mm"

theorem isdrngo1
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  assume isdivrng1.1: |- G = ( 1st ` R )
  assume isdivrng1.2: |- H = ( 2nd ` R )
  assume isdivrng1.3: |- Z = ( GId ` G )
  assume isdivrng1.4: |- X = ran G


  assert |- ( R e. DivRingOps <-> ( R e. RingOps /\ ( H |` ( ( X \ { Z } ) X. ( X \ { Z } ) ) ) e. GrpOp ) )

  proof
    cR
    cdrng
    wcel
    #
    cR
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
    wceq
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
    cdrng
    wrel
    @0
    @4
    vg
    cv
    #
    vh
    cv
    #
    cop
    crngo
    wcel
    @13
    @12
    crn
    @12
    cgi
    cfv
    csn
    cdif
    #
    @14
    cxp
    cres
    cgr
    wcel
    wa
    vg
    vh
    cdrng
    vg
    vh
    df-drngo
    relopabi
    cR
    cdrng
    1st2nd
    mpan
    @5
    @4
    @10
    crngo
    wrel
    @5
    @4
    relrngo
    cR
    crngo
    1st2nd
    mpan
    adantr
    @4
    cR
    cG
    cH
    cop
    #
    wceq
    #
    @0
    @11
    wb
    #
    @15
    @3
    cR
    cG
    @1
    cH
    @2
    isdivrng1.1
    isdivrng1.2
    opeq12i
    eqeq2i
    @16
    @17
    @15
    cdrng
    wcel
    #
    @15
    crngo
    wcel
    #
    @10
    wa
    #
    wb
    @18
    @19
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
    @20
    cH
    cvv
    wcel
    @18
    @28
    wb
    cH
    @2
    cvv
    isdivrng1.2
    cR
    c2nd
    fvex
    eqeltri
    cvv
    cG
    cH
    isdivrngo
    ax-mp
    @10
    @27
    @19
    @9
    @26
    cgr
    @8
    @25
    cH
    @7
    @24
    @7
    @24
    cX
    @21
    @6
    @23
    isdivrng1.4
    cZ
    @22
    isdivrng1.3
    sneqi
    difeq12i
    #
    @29
    xpeq12i
    reseq2i
    eleq1i
    anbi2i
    bitr4i
    @16
    @0
    @18
    @11
    @20
    cR
    @15
    cdrng
    eleq1
    @16
    @5
    @19
    @10
    cR
    @15
    crngo
    eleq1
    anbi1d
    bibi12d
    mpbiri
    sylbir
    pm5.21nii
end
