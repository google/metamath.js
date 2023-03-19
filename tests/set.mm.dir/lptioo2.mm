include "cioo.mm"
include "co.mm"
include "clp.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cxr.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "difssd.mm"
include "simpr.mm"
include "wn.mm"
include "ubioo.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "mtoi.mm"
include "adantl.mm"
include "velsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ineq2d.mm"
include "ad2antrr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "simplrl.mm"
include "simplrr.mm"
include "w3a.mm"
include "clt.mm"
include "elioo3g.mm"
include "biimpi.mm"
include "simpld.mm"
include "simp3d.mm"
include "iooin.mm"
include "syl22anc.mm"
include "iftrue.mm"
include "ad3antrrr.mm"
include "eqbrtrd.mm"
include "iffalse.mm"
include "simprd.mm"
include "ad2antlr.mm"
include "pm2.61dan.mm"
include "wb.mm"
include "simp2d.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "syl.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "ifcld.mm"
include "eqeltrrd.mm"
include "ioon0.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "ralrimivva.mm"
include "cr.mm"
include "wss.mm"
include "ioossre.mm"
include "a1i.mm"
include "islptre.mm"

theorem lptioo2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lptioo2.1: |- J = ( topGen ` ran (,) )
  assume lptioo2.2: |- ( ph -> A e. RR* )
  assume lptioo2.3: |- ( ph -> B e. RR )
  assume lptioo2.4: |- ( ph -> A < B )


  assert |- ( ph -> B e. ( ( limPt ` J ) ` ( A (,) B ) ) )

  proof
    wph
    cB
    cA
    cB
    cioo
    co
    #
    cJ
    clp
    cfv
    cfv
    wcel
    cB
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wcel
    #
    @3
    @0
    cB
    csn
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    wi
    #
    vb
    cxr
    wral
    va
    cxr
    wral
    wph
    @9
    va
    vb
    cxr
    cxr
    wph
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    wa
    #
    wa
    #
    @4
    @8
    @13
    @4
    wa
    #
    @7
    @3
    @0
    cin
    #
    c0
    wph
    @7
    @15
    wceq
    @12
    @4
    wph
    @6
    @0
    @3
    wph
    @6
    @0
    wph
    @0
    @5
    difssd
    wph
    vx
    @0
    @6
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @16
    @6
    wcel
    wph
    @17
    wa
    #
    @16
    @0
    @5
    wph
    @17
    simpr
    @18
    @16
    cB
    wceq
    #
    @16
    @5
    wcel
    @17
    @19
    wn
    wph
    @17
    @19
    cB
    @0
    wcel
    #
    cA
    cB
    ubioo
    @19
    @17
    @20
    @16
    cB
    @0
    eleq1
    biimpcd
    mtoi
    adantl
    vx
    cB
    velsn
    sylnibr
    eldifd
    ex
    ssrdv
    eqssd
    ineq2d
    ad2antrr
    @14
    @15
    @1
    cA
    cle
    wbr
    #
    cA
    @1
    cif
    #
    @2
    cB
    cle
    wbr
    #
    @2
    cB
    cif
    #
    cioo
    co
    #
    c0
    @14
    @10
    @11
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @15
    @25
    wceq
    wph
    @10
    @11
    @4
    simplrl
    #
    wph
    @10
    @11
    @4
    simplrr
    wph
    @26
    @12
    @4
    lptioo2.2
    ad2antrr
    #
    @4
    @27
    @13
    @4
    @10
    @11
    @27
    @4
    @10
    @11
    @27
    w3a
    #
    @1
    cB
    clt
    wbr
    #
    cB
    @2
    clt
    wbr
    #
    wa
    #
    @4
    @30
    @33
    wa
    @1
    @2
    cB
    elioo3g
    biimpi
    #
    simpld
    #
    simp3d
    #
    adantl
    #
    @1
    @2
    cA
    cB
    iooin
    syl22anc
    @14
    @25
    c0
    wne
    #
    @22
    @24
    clt
    wbr
    #
    @14
    @22
    cB
    @24
    clt
    @14
    @21
    @22
    cB
    clt
    wbr
    @14
    @21
    wa
    @22
    cA
    cB
    clt
    @21
    @22
    cA
    wceq
    @14
    @21
    cA
    @1
    iftrue
    adantl
    wph
    cA
    cB
    clt
    wbr
    @12
    @4
    @21
    lptioo2.4
    ad3antrrr
    eqbrtrd
    @14
    @21
    wn
    #
    wa
    @22
    @1
    cB
    clt
    @40
    @22
    @1
    wceq
    @14
    @21
    cA
    @1
    iffalse
    adantl
    @4
    @31
    @13
    @40
    @4
    @31
    @32
    @4
    @30
    @33
    @34
    simprd
    #
    simpld
    ad2antlr
    eqbrtrd
    pm2.61dan
    @4
    cB
    @24
    wceq
    @13
    @4
    @24
    cB
    @4
    @23
    wn
    #
    @24
    cB
    wceq
    @4
    @32
    @42
    @4
    @31
    @32
    @41
    simprd
    @4
    @27
    @11
    @32
    @42
    wb
    @36
    @4
    @10
    @11
    @27
    @35
    simp2d
    cB
    @2
    xrltnle
    syl2anc
    mpbid
    @23
    @2
    cB
    iffalse
    syl
    eqcomd
    adantl
    #
    breqtrd
    @14
    @22
    cxr
    wcel
    @24
    cxr
    wcel
    @38
    @39
    wb
    @14
    @21
    cA
    @1
    cxr
    @29
    @28
    ifcld
    @14
    cB
    @24
    cxr
    @43
    @37
    eqeltrrd
    @22
    @24
    ioon0
    syl2anc
    mpbird
    eqnetrd
    eqnetrd
    ex
    ralrimivva
    wph
    @0
    cB
    cJ
    va
    vb
    lptioo2.1
    @0
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    lptioo2.3
    islptre
    mpbird
end
