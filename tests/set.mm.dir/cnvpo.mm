include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "ccnv.mm"
include "wpo.mm"
include "r19.26.mm"
include "weq.mm"
include "vex.mm"
include "brcnv.mm"
include "id.mm"
include "breq12d.mm"
include "syl5bb.mm"
include "notbid.mm"
include "cbvralv.mm"
include "anbi12ci.mm"
include "imbi12i.mm"
include "ralbii.mm"
include "anbi12i.mm"
include "bitr2i.mm"
include "ralidm.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "rzal.mm"
include "2thd.mm"
include "wne.mm"
include "r19.3rzv.mm"
include "ralbidv.mm"
include "pm2.61ine.mm"
include "anbi1i.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "ralcom.mm"
include "df-po.mm"

theorem cnvpo
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Po A <-> `' R Po A )

  proof
    vx
    cv
    #
    @0
    cR
    wbr
    #
    wn
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    @3
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @0
    @5
    cR
    wbr
    #
    wi
    #
    wa
    vz
    cA
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @5
    @5
    cR
    ccnv
    #
    wbr
    #
    wn
    #
    @5
    @3
    @12
    wbr
    #
    @3
    @0
    @12
    wbr
    #
    wa
    #
    @5
    @0
    @12
    wbr
    #
    wi
    #
    wa
    #
    vx
    cA
    wral
    #
    vy
    cA
    wral
    vz
    cA
    wral
    #
    cA
    cR
    wpo
    cA
    @12
    wpo
    @10
    vx
    cA
    wral
    #
    vy
    cA
    wral
    @21
    vz
    cA
    wral
    #
    vy
    cA
    wral
    @11
    @22
    @23
    @24
    vy
    cA
    @2
    vx
    cA
    wral
    #
    @9
    vz
    cA
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    @20
    vz
    cA
    wral
    #
    vx
    cA
    wral
    @23
    @24
    @27
    @29
    vx
    cA
    @29
    @14
    vz
    cA
    wral
    #
    @19
    vz
    cA
    wral
    #
    wa
    @27
    @14
    @19
    vz
    cA
    r19.26
    @30
    @25
    @31
    @26
    @14
    @2
    vz
    vx
    cA
    vz
    vx
    weq
    #
    @13
    @1
    @13
    @5
    @5
    cR
    wbr
    @32
    @1
    @5
    @5
    cR
    vz
    vex
    #
    @33
    brcnv
    @32
    @5
    @0
    @5
    @0
    cR
    @32
    id
    #
    @34
    breq12d
    syl5bb
    notbid
    cbvralv
    @19
    @9
    vz
    cA
    @17
    @7
    @18
    @8
    @15
    @6
    @16
    @4
    @5
    @3
    cR
    @33
    vy
    vex
    #
    brcnv
    @3
    @0
    cR
    @35
    vx
    vex
    #
    brcnv
    anbi12ci
    @5
    @0
    cR
    @33
    @36
    brcnv
    imbi12i
    ralbii
    anbi12i
    bitr2i
    ralbii
    @2
    vz
    cA
    wral
    #
    @26
    wa
    #
    vx
    cA
    wral
    #
    @25
    vx
    cA
    wral
    #
    @26
    vx
    cA
    wral
    #
    wa
    #
    @23
    @28
    @39
    @37
    vx
    cA
    wral
    #
    @41
    wa
    @42
    @37
    @26
    vx
    cA
    r19.26
    @43
    @40
    @41
    @40
    @25
    @43
    @2
    vx
    cA
    ralidm
    @25
    @43
    wb
    cA
    c0
    cA
    c0
    wceq
    @25
    @43
    @2
    vx
    cA
    rzal
    @37
    vx
    cA
    rzal
    2thd
    cA
    c0
    wne
    @2
    @37
    vx
    cA
    @2
    vz
    cA
    r19.3rzv
    ralbidv
    pm2.61ine
    bitr2i
    anbi1i
    bitri
    @10
    @38
    vx
    cA
    @2
    @9
    vz
    cA
    r19.26
    ralbii
    @25
    @26
    vx
    cA
    r19.26
    3bitr4i
    @20
    vz
    vx
    cA
    cA
    ralcom
    3bitr4i
    ralbii
    @10
    vx
    vy
    cA
    cA
    ralcom
    @21
    vz
    vy
    cA
    cA
    ralcom
    3bitr4i
    vx
    vy
    vz
    cA
    cR
    df-po
    vz
    vy
    vx
    cA
    @12
    df-po
    3bitr4i
end
