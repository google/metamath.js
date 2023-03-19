include "cdmn.mm"
include "wcel.mm"
include "cprrng.mm"
include "ccring.mm"
include "wa.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "isdmn2.mm"
include "crngo.mm"
include "csn.mm"
include "cpridl.mm"
include "cfv.mm"
include "isprrngo.mm"
include "cidl.mm"
include "ispridlc.mm"
include "crngorngo.mm"
include "biantrurd.mm"
include "3anass.mm"
include "0idl.mm"
include "syl.mm"
include "wb.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "eleq2.mm"
include "elsni.mm"
include "syl6bir.mm"
include "syl5com.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "rngoueqz.mm"
include "rngo0cl.mm"
include "en1eqsn.mm"
include "eqcomd.mm"
include "ex.mm"
include "sylbird.mm"
include "impbid.mm"
include "necon3bid.mm"
include "ovex.mm"
include "elsn.mm"
include "velsn.mm"
include "orbi12i.mm"
include "imbi12i.mm"
include "a1i.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "3bitr3d.mm"
include "pm5.32i.mm"
include "ancom.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem isdmn3
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume isdmn3.1: |- G = ( 1st ` R )
  assume isdmn3.2: |- H = ( 2nd ` R )
  assume isdmn3.3: |- X = ran G
  assume isdmn3.4: |- Z = ( GId ` G )
  assume isdmn3.5: |- U = ( GId ` H )

  disjoint R a
  disjoint R b
  disjoint a b
  disjoint Z a
  disjoint Z b
  disjoint H a
  disjoint H b
  disjoint X a
  disjoint X b
  assert |- ( R e. Dmn <-> ( R e. CRingOps /\ U =/= Z /\ A. a e. X A. b e. X ( ( a H b ) = Z -> ( a = Z \/ b = Z ) ) ) )

  proof
    cR
    cdmn
    wcel
    cR
    cprrng
    wcel
    #
    cR
    ccring
    wcel
    #
    wa
    #
    @1
    cU
    cZ
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    cH
    co
    #
    cZ
    wceq
    #
    @4
    cZ
    wceq
    #
    @5
    cZ
    wceq
    #
    wo
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    w3a
    #
    cR
    isdmn2
    @1
    @0
    wa
    @1
    @3
    @12
    wa
    #
    wa
    @2
    @13
    @1
    @0
    @14
    @0
    cR
    crngo
    wcel
    #
    cZ
    csn
    #
    cR
    cpridl
    cfv
    wcel
    #
    wa
    #
    @1
    @14
    cR
    cG
    cZ
    isdmn3.1
    isdmn3.4
    isprrngo
    @1
    @17
    @16
    cR
    cidl
    cfv
    wcel
    #
    @16
    cX
    wne
    #
    @6
    @16
    wcel
    #
    @4
    @16
    wcel
    #
    @5
    @16
    wcel
    #
    wo
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    w3a
    #
    @18
    @14
    @16
    cR
    cG
    cH
    cX
    va
    vb
    isdmn3.1
    isdmn3.2
    isdmn3.3
    ispridlc
    @1
    @15
    @17
    cR
    crngorngo
    #
    biantrurd
    @27
    @19
    @20
    @26
    wa
    #
    wa
    #
    @1
    @14
    @19
    @20
    @26
    3anass
    @1
    @29
    @30
    @14
    @1
    @19
    @29
    @1
    @15
    @19
    @28
    cR
    cG
    cZ
    isdmn3.1
    isdmn3.4
    0idl
    syl
    biantrurd
    @1
    @20
    @3
    @26
    @12
    @1
    @16
    cX
    cU
    cZ
    @1
    @15
    @16
    cX
    wceq
    #
    cU
    cZ
    wceq
    #
    wb
    @28
    @15
    @31
    @32
    @15
    cU
    cX
    wcel
    #
    @31
    @32
    cR
    cU
    cH
    cX
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    isdmn3.3
    cG
    @34
    isdmn3.1
    rneqi
    eqtri
    isdmn3.2
    isdmn3.5
    rngo1cl
    @31
    @33
    cU
    @16
    wcel
    @32
    @16
    cX
    cU
    eleq2
    cU
    cZ
    elsni
    syl6bir
    syl5com
    @15
    @32
    cX
    c1o
    cen
    wbr
    #
    @31
    cR
    cU
    cG
    cH
    cX
    cZ
    isdmn3.1
    isdmn3.2
    isdmn3.4
    isdmn3.5
    isdmn3.3
    rngoueqz
    @15
    cZ
    cX
    wcel
    #
    @35
    @31
    wi
    cR
    cG
    cX
    cZ
    isdmn3.1
    isdmn3.3
    isdmn3.4
    rngo0cl
    @36
    @35
    @31
    @36
    @35
    wa
    cX
    @16
    cZ
    cX
    en1eqsn
    eqcomd
    ex
    syl
    sylbird
    impbid
    syl
    necon3bid
    @1
    @25
    @11
    va
    vb
    cX
    cX
    @25
    @11
    wb
    @1
    @21
    @7
    @24
    @10
    @6
    cZ
    @4
    @5
    cH
    ovex
    elsn
    @22
    @8
    @23
    @9
    va
    cZ
    velsn
    vb
    cZ
    velsn
    orbi12i
    imbi12i
    a1i
    2ralbidv
    anbi12d
    bitr3d
    syl5bb
    3bitr3d
    syl5bb
    pm5.32i
    @0
    @1
    ancom
    @1
    @3
    @12
    3anass
    3bitr4i
    bitri
end
