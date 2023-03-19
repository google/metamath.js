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
include "lbioo.mm"
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
include "rexrd.mm"
include "jca.mm"
include "iooin.mm"
include "syl21anc.mm"
include "clt.mm"
include "w3a.mm"
include "elioo3g.mm"
include "biimpi.mm"
include "simpld.mm"
include "simp1d.mm"
include "simp3d.mm"
include "simprd.mm"
include "xrltled.mm"
include "iftrued.mm"
include "ad2antlr.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "ad3antrrr.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "adantr.mm"
include "ifclda.mm"
include "ioon0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "ralrimivva.mm"
include "cr.mm"
include "wss.mm"
include "ioossre.mm"
include "a1i.mm"
include "islptre.mm"

theorem lptioo1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lptioo1.1: |- J = ( topGen ` ran (,) )
  assume lptioo1.2: |- ( ph -> A e. RR )
  assume lptioo1.3: |- ( ph -> B e. RR* )
  assume lptioo1.4: |- ( ph -> A < B )


  assert |- ( ph -> A e. ( ( limPt ` J ) ` ( A (,) B ) ) )

  proof
    wph
    cA
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
    cA
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
    cA
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
    cA
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
    cA
    @0
    wcel
    #
    cA
    cB
    lbioo
    @19
    @17
    @20
    @16
    cA
    @0
    eleq1
    biimpcd
    mtoi
    adantl
    vx
    cA
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
    wa
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
    #
    wph
    @28
    @12
    @4
    wph
    @26
    @27
    wph
    cA
    lptioo1.2
    rexrd
    #
    lptioo1.3
    jca
    ad2antrr
    @1
    @2
    cA
    cB
    iooin
    syl21anc
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
    cA
    @24
    clt
    @4
    @22
    cA
    wceq
    @13
    @4
    @21
    cA
    @1
    @4
    @1
    cA
    @4
    @10
    @11
    @26
    @4
    @10
    @11
    @26
    w3a
    #
    @1
    cA
    clt
    wbr
    #
    cA
    @2
    clt
    wbr
    #
    wa
    #
    @4
    @34
    @37
    wa
    @1
    @2
    cA
    elioo3g
    biimpi
    #
    simpld
    #
    simp1d
    @4
    @10
    @11
    @26
    @39
    simp3d
    @4
    @35
    @36
    @4
    @34
    @37
    @38
    simprd
    #
    simpld
    xrltled
    iftrued
    adantl
    @14
    @23
    cA
    @24
    clt
    wbr
    @14
    @23
    wa
    cA
    @2
    @24
    clt
    @4
    @36
    @13
    @23
    @4
    @35
    @36
    @40
    simprd
    ad2antlr
    @23
    @2
    @24
    wceq
    @14
    @23
    @24
    @2
    @23
    @2
    cB
    iftrue
    eqcomd
    adantl
    breqtrd
    @14
    @23
    wn
    #
    wa
    cA
    cB
    @24
    clt
    wph
    cA
    cB
    clt
    wbr
    @12
    @4
    @41
    lptioo1.4
    ad3antrrr
    @41
    cB
    @24
    wceq
    @14
    @41
    @24
    cB
    @23
    @2
    cB
    iffalse
    eqcomd
    adantl
    breqtrd
    pm2.61dan
    eqbrtrd
    @14
    @22
    cxr
    wcel
    @24
    cxr
    wcel
    @32
    @33
    wb
    @14
    @21
    cA
    @1
    cxr
    wph
    @26
    @12
    @4
    @21
    @31
    ad3antrrr
    @14
    @10
    @21
    wn
    @29
    adantr
    ifclda
    @14
    @23
    @2
    cB
    cxr
    @14
    @11
    @23
    @30
    adantr
    wph
    @27
    @12
    @4
    @41
    lptioo1.3
    ad3antrrr
    ifclda
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
    cA
    cJ
    va
    vb
    lptioo1.1
    @0
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    lptioo1.2
    islptre
    mpbird
end
