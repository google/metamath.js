include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "df-ral.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "opelresi.mm"
include "ax-mp.mm"
include "df-br.mm"
include "bicomi.mm"
include "imbi12i.mm"
include "albii.mm"
include "ralidm.mm"
include "ralv.mm"
include "bitri.mm"
include "cxp.mm"
include "pm2.27.mm"
include "wa.mm"
include "opelresg.mm"
include "weq.mm"
include "ideq.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "syl6.mm"
include "syl6bir.mm"
include "pm2.43i.mm"
include "com3r.mm"
include "sylbi.mm"
include "sylbir.mm"
include "imp.mm"
include "syl6bi.mm"
include "ralrimiv.mm"
include "sps.mm"
include "ralimi.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "wrel.mm"
include "relres.mm"
include "df-rel.mm"
include "mpbi.mm"
include "sseli.mm"
include "ancri.mm"
include "pm3.31.mm"
include "syl5.mm"
include "alimi.mm"
include "syl.mm"
include "dfss2.mm"
include "ssel.mm"
include "alrimiv.mm"
include "impbii.mm"
include "3bitr2ri.mm"

theorem issref
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint R x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V z
  disjoint W z
  assert |- ( ( _I |` A ) C_ R <-> A. x e. A x R x )

  proof
    vx
    cv
    #
    @0
    cR
    wbr
    #
    vx
    cA
    wral
    @0
    cA
    wcel
    #
    @1
    wi
    #
    vx
    wal
    @0
    @0
    cop
    #
    cid
    cA
    cres
    #
    wcel
    #
    @4
    cR
    wcel
    #
    wi
    #
    vx
    wal
    #
    @5
    cR
    wss
    #
    @1
    vx
    cA
    df-ral
    @8
    @3
    vx
    @6
    @2
    @7
    @1
    @0
    cvv
    wcel
    #
    @6
    @2
    wb
    vx
    vex
    #
    @0
    cA
    cvv
    opelresi
    ax-mp
    @1
    @7
    @0
    @0
    cR
    df-br
    bicomi
    imbi12i
    albii
    @9
    @10
    @9
    vy
    cv
    #
    @5
    wcel
    #
    @13
    cR
    wcel
    #
    wi
    #
    vy
    wal
    #
    @10
    @9
    @8
    vx
    cvv
    wral
    #
    vx
    cvv
    wral
    #
    @17
    @19
    @18
    @9
    @8
    vx
    cvv
    ralidm
    @8
    vx
    ralv
    bitri
    @19
    @16
    vy
    cvv
    cvv
    cxp
    #
    wral
    #
    @17
    @19
    @0
    vz
    cv
    #
    cop
    #
    @5
    wcel
    #
    @23
    cR
    wcel
    #
    wi
    #
    vz
    cvv
    wral
    #
    vx
    cvv
    wral
    @21
    @18
    @27
    vx
    cvv
    @18
    @11
    @8
    wi
    #
    vx
    wal
    @27
    @8
    vx
    cvv
    df-ral
    @28
    @27
    vx
    @11
    @28
    @27
    wi
    @12
    @11
    @28
    @8
    @27
    @11
    @8
    pm2.27
    @8
    @26
    vz
    cvv
    @22
    cvv
    wcel
    #
    @24
    @8
    @25
    @29
    @24
    @23
    cid
    wcel
    #
    @2
    wa
    @8
    @25
    wi
    #
    @0
    @22
    cid
    cA
    cvv
    opelresg
    @30
    @2
    @31
    @30
    @0
    @22
    cid
    wbr
    #
    @2
    @31
    wi
    #
    @0
    @22
    cid
    df-br
    @32
    vx
    vz
    weq
    #
    @33
    @0
    @22
    vz
    vex
    ideq
    @2
    @8
    @34
    @25
    @2
    @8
    @34
    @25
    wi
    #
    wi
    #
    @2
    @2
    @6
    @36
    @0
    cA
    cA
    opelresi
    @6
    @8
    @7
    @35
    @6
    @7
    pm2.27
    @34
    @7
    @25
    @34
    @4
    @23
    cR
    @0
    @22
    @0
    opeq2
    eleq1d
    biimpcd
    syl6
    syl6bir
    pm2.43i
    com3r
    sylbi
    sylbir
    imp
    syl6bi
    com3r
    ralrimiv
    syl6
    ax-mp
    sps
    sylbi
    ralimi
    @16
    @26
    vy
    vx
    vz
    cvv
    cvv
    @13
    @23
    wceq
    @14
    @24
    @15
    @25
    @13
    @23
    @5
    eleq1
    @13
    @23
    cR
    eleq1
    imbi12d
    ralxp
    sylibr
    @21
    @13
    @20
    wcel
    #
    @16
    wi
    #
    vy
    wal
    @17
    @16
    vy
    @20
    df-ral
    @38
    @16
    vy
    @14
    @37
    @14
    wa
    @38
    @15
    @14
    @37
    @5
    @20
    @13
    @5
    wrel
    @5
    @20
    wss
    cid
    cA
    relres
    @5
    df-rel
    mpbi
    sseli
    ancri
    @37
    @14
    @15
    pm3.31
    syl5
    alimi
    sylbi
    syl
    sylbir
    vy
    @5
    cR
    dfss2
    sylibr
    @10
    @8
    vx
    @5
    cR
    @4
    ssel
    alrimiv
    impbii
    3bitr2ri
end
