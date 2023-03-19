include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "cdif.mm"
include "cun.mm"
include "df-sup.mm"
include "cab.mm"
include "cin.mm"
include "dfrab3.mm"
include "cvv.mm"
include "wceq.mm"
include "wcel.mm"
include "wb.mm"
include "abeq1.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "wo.mm"
include "elima.mm"
include "dfrex2.mm"
include "bitri.mm"
include "orbi12i.mm"
include "elun.mm"
include "ianor.mm"
include "3bitr4i.mm"
include "con2bii.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "impexp.mm"
include "imbi1i.mm"
include "rexbii.mm"
include "imbi2i.mm"
include "con34b.mm"
include "bitr3i.mm"
include "ralbii2.mm"
include "anbi12i.mm"
include "3bitr2ri.mm"
include "mpgbir.mm"
include "ineq2i.mm"
include "invdif.mm"
include "eqtri.mm"
include "unieqi.mm"

theorem dfsup2
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- sup ( B , A , R ) = U. ( A \ ( ( `' R " B ) u. ( R " ( A \ ( `' R " B ) ) ) ) )

  proof
    cB
    cA
    cR
    csup
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @1
    @0
    cR
    wbr
    #
    @1
    vz
    cv
    #
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    crab
    #
    cuni
    cA
    cR
    ccnv
    #
    cB
    cima
    #
    cR
    cA
    @14
    cdif
    #
    cima
    #
    cun
    #
    cdif
    #
    cuni
    vx
    vy
    vz
    cB
    cA
    cR
    df-sup
    @12
    @18
    @12
    cA
    @11
    vx
    cab
    #
    cin
    #
    @18
    @11
    vx
    cA
    dfrab3
    @20
    cA
    cvv
    @17
    cdif
    #
    cin
    @18
    @19
    @21
    cA
    @19
    @21
    wceq
    @11
    @0
    @21
    wcel
    #
    wb
    vx
    @11
    vx
    @21
    abeq1
    @22
    @0
    @17
    wcel
    #
    wn
    #
    @1
    @0
    @13
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @5
    wn
    #
    vy
    @15
    wral
    #
    wa
    #
    @11
    @22
    @0
    cvv
    wcel
    @24
    vx
    vex
    #
    @0
    cvv
    @17
    eldif
    mpbiran
    @23
    @30
    @0
    @14
    wcel
    #
    @0
    @16
    wcel
    #
    wo
    @27
    wn
    #
    @29
    wn
    #
    wo
    @23
    @30
    wn
    @32
    @34
    @33
    @35
    @32
    @25
    vy
    cB
    wrex
    @34
    vy
    @0
    @13
    cB
    @31
    elima
    @25
    vy
    cB
    dfrex2
    bitri
    @33
    @5
    vy
    @15
    wrex
    @35
    vy
    @0
    cR
    @15
    @31
    elima
    @5
    vy
    @15
    dfrex2
    bitri
    orbi12i
    @0
    @14
    @16
    elun
    @27
    @29
    ianor
    3bitr4i
    con2bii
    @27
    @4
    @29
    @10
    @26
    @3
    vy
    cB
    @25
    @2
    @1
    @0
    cR
    vy
    vex
    #
    @31
    brcnv
    notbii
    ralbii
    @28
    @9
    vy
    @15
    cA
    @1
    cA
    wcel
    #
    @1
    @14
    wcel
    #
    wn
    #
    wa
    #
    @28
    wi
    @37
    @39
    @28
    wi
    #
    wi
    @1
    @15
    wcel
    #
    @28
    wi
    @37
    @9
    wi
    @37
    @39
    @28
    impexp
    @42
    @40
    @28
    @1
    cA
    @14
    eldif
    imbi1i
    @9
    @41
    @37
    @9
    @5
    @38
    wi
    @41
    @38
    @8
    @5
    @38
    @6
    @1
    @13
    wbr
    #
    vz
    cB
    wrex
    @8
    vz
    @1
    @13
    cB
    @36
    elima
    @43
    @7
    vz
    cB
    @6
    @1
    cR
    vz
    vex
    @36
    brcnv
    rexbii
    bitri
    imbi2i
    @5
    @38
    con34b
    bitr3i
    imbi2i
    3bitr4i
    ralbii2
    anbi12i
    3bitr2ri
    mpgbir
    ineq2i
    cA
    @17
    invdif
    eqtri
    eqtri
    unieqi
    eqtri
end
