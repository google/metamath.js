include "wral.mm"
include "cv.mm"
include "c-bnj18.mm"
include "wcel.mm"
include "wn.mm"
include "w-bnj15.mm"
include "wi.mm"
include "biimpi.mm"
include "w3a.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wo.mm"
include "wbr.mm"
include "bnj1418.mm"
include "adantl.mm"
include "wfr.mm"
include "bnj835.mm"
include "w-bnj13.mm"
include "df-bnj15.mm"
include "simplbi.mm"
include "syl.mm"
include "bnj213.mm"
include "sseli.mm"
include "frirr.mm"
include "syl2an.mm"
include "pm2.65da.mm"
include "wrex.mm"
include "nfv.mm"
include "wsbc.mm"
include "bnj1095.mm"
include "nf5i.mm"
include "nf3an.mm"
include "nfxfr.mm"
include "wa.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldi.mm"
include "simpr.mm"
include "bnj1125.mm"
include "syl3anc.mm"
include "bnj1147.mm"
include "bnj906.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "bnj837.mm"
include "ad2antlr.mm"
include "rsp.mm"
include "syl3c.mm"
include "vex.mm"
include "weq.mm"
include "eleq1.mm"
include "bnj1318.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "notbid.mm"
include "syl5bb.mm"
include "sbcie.mm"
include "sylib.mm"
include "ex.mm"
include "ralrimi.mm"
include "ralnex.mm"
include "eliun.mm"
include "sylnibr.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "simp2bi.mm"
include "bnj1414.mm"
include "bnj1138.mm"
include "syl6bb.mm"
include "mtbird.mm"
include "sylibr.mm"
include "sylbir.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "bnj1204.mm"
include "ralbii.mm"

theorem bnj1417
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume bnj1417.1: |- ( ph <-> R _FrSe A )
  assume bnj1417.2: |- ( ps <-> -. x e. _trCl ( x , A , R ) )
  assume bnj1417.3: |- ( ch <-> A. y e. A ( y R x -> [. y / x ]. ps ) )
  assume bnj1417.4: |- ( th <-> ( ph /\ x e. A /\ ch ) )
  assume bnj1417.5: |- B = ( _pred ( x , A , R ) u. U_ y e. _pred ( x , A , R ) _trCl ( y , A , R ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  assert |- ( ph -> A. x e. A -. x e. _trCl ( x , A , R ) )

  proof
    wph
    wps
    vx
    cA
    wral
    #
    vx
    cv
    #
    cA
    cR
    @1
    c-bnj18
    #
    wcel
    #
    wn
    #
    vx
    cA
    wral
    wph
    cA
    cR
    w-bnj15
    #
    wch
    wps
    wi
    #
    vx
    cA
    wral
    @0
    wph
    @5
    bnj1417.1
    biimpi
    #
    wph
    @6
    vx
    cA
    wph
    @1
    cA
    wcel
    #
    wch
    wps
    wph
    @8
    wch
    w3a
    #
    wth
    wps
    bnj1417.4
    wth
    @4
    wps
    wth
    @3
    @1
    cA
    cR
    @1
    c-bnj14
    #
    wcel
    #
    @1
    vy
    @10
    cA
    cR
    vy
    cv
    #
    c-bnj18
    #
    ciun
    #
    wcel
    #
    wo
    #
    wth
    @11
    wn
    @15
    wn
    @16
    wn
    wth
    @11
    @1
    @1
    cR
    wbr
    #
    @11
    @17
    wth
    vx
    vx
    cA
    cR
    bnj1418
    adantl
    wth
    cA
    cR
    wfr
    #
    @8
    @17
    wn
    @11
    wth
    @5
    @18
    wph
    @8
    wch
    @5
    wth
    bnj1417.4
    @7
    bnj835
    #
    @5
    @18
    cA
    cR
    w-bnj13
    cA
    cR
    df-bnj15
    simplbi
    syl
    @10
    cA
    @1
    cA
    cR
    @1
    bnj213
    #
    sseli
    cA
    @1
    cR
    frirr
    syl2an
    pm2.65da
    wth
    @1
    @13
    wcel
    #
    vy
    @10
    wrex
    #
    @15
    wth
    @21
    wn
    #
    vy
    @10
    wral
    @22
    wn
    wth
    @23
    vy
    @10
    wth
    @9
    vy
    bnj1417.4
    wph
    @8
    wch
    vy
    wph
    vy
    nfv
    @8
    vy
    nfv
    wch
    vy
    wch
    @12
    @1
    cR
    wbr
    #
    wps
    vx
    @12
    wsbc
    #
    wi
    #
    vy
    cA
    bnj1417.3
    bnj1095
    nf5i
    nf3an
    nfxfr
    wth
    @12
    @10
    wcel
    #
    @23
    wth
    @27
    wa
    #
    @21
    @12
    @13
    wcel
    #
    @28
    @21
    wa
    #
    @2
    @13
    @12
    @30
    @5
    @12
    cA
    wcel
    #
    @21
    @2
    @13
    wss
    wth
    @5
    @27
    @21
    @19
    ad2antrr
    #
    @30
    @10
    cA
    @12
    @20
    wth
    @27
    @21
    simplr
    #
    sseldi
    #
    @28
    @21
    simpr
    #
    cA
    cR
    @12
    @1
    bnj1125
    syl3anc
    @30
    @10
    @2
    @12
    @30
    @5
    @8
    @10
    @2
    wss
    @32
    @30
    @13
    cA
    @1
    cA
    cR
    @12
    bnj1147
    @35
    sseldi
    cA
    cR
    @1
    bnj906
    syl2anc
    @33
    sseldd
    sseldd
    @30
    @25
    @29
    wn
    #
    @30
    @26
    vy
    cA
    wral
    #
    @31
    @24
    @25
    wth
    @37
    @27
    @21
    wph
    @8
    wch
    @37
    wth
    bnj1417.4
    wch
    @37
    bnj1417.3
    biimpi
    bnj837
    ad2antrr
    @34
    @27
    @24
    wth
    @21
    vx
    vy
    cA
    cR
    bnj1418
    ad2antlr
    @26
    vy
    cA
    rsp
    syl3c
    wps
    @36
    vx
    @12
    vy
    vex
    wps
    @4
    vx
    vy
    weq
    #
    @36
    bnj1417.2
    @38
    @3
    @29
    @38
    @3
    @12
    @2
    wcel
    @29
    @1
    @12
    @2
    eleq1
    @38
    @2
    @13
    @12
    cA
    cR
    @1
    @12
    bnj1318
    eleq2d
    bitrd
    notbid
    syl5bb
    sbcie
    sylib
    pm2.65da
    ex
    ralrimi
    @21
    vy
    @10
    ralnex
    sylib
    vy
    @1
    @10
    @13
    eliun
    sylnibr
    @11
    @15
    ioran
    sylanbrc
    wth
    @3
    @1
    cB
    wcel
    @16
    wth
    @2
    cB
    @1
    wth
    @5
    @8
    @2
    cB
    wceq
    @19
    wth
    wph
    @8
    wch
    bnj1417.4
    simp2bi
    vy
    cA
    cB
    cR
    @1
    bnj1417.5
    bnj1414
    syl2anc
    eleq2d
    cB
    @10
    @14
    @1
    bnj1417.5
    bnj1138
    syl6bb
    mtbird
    bnj1417.2
    sylibr
    sylbir
    3exp
    ralrimiv
    wps
    wch
    vx
    vy
    cA
    cR
    bnj1417.3
    bnj1204
    syl2anc
    wps
    @4
    vx
    cA
    bnj1417.2
    ralbii
    sylib
end
