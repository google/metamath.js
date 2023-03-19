include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "w3a.mm"
include "eqid.mm"
include "islshpsm.mm"
include "wa.mm"
include "wex.mm"
include "df-3an.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "c0g.mm"
include "cdif.mm"
include "df-rex.mm"
include "simpr.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "clmod.mm"
include "ad3antrrr.mm"
include "lspsn0.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "csubg.mm"
include "simplrl.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "lsm01.mm"
include "simplrr.mm"
include "eqnetrd.mm"
include "ex.mm"
include "necon2d.mm"
include "pm4.71rd.mm"
include "pm5.32da.mm"
include "eldifsn.mm"
include "anbi1i.mm"
include "anass.mm"
include "an12.mm"
include "anbi2i.mm"
include "bitri.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "fvex.mm"
include "rexcom4b.mm"
include "ancom.mm"
include "rexbii.mm"
include "exbii.mm"
include "r19.41v.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "pm5.32i.mm"
include "bitr3i.mm"
include "syl6bbr.mm"
include "wb.mm"
include "islsat.mm"
include "anbi1d.mm"
include "bitr4d.mm"
include "bitrd.mm"

theorem islshpat
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cV: class V
  let cW: class W
  let vq: setvar q
  let vv: setvar v
  assume islshpat.v: |- V = ( Base ` W )
  assume islshpat.s: |- S = ( LSubSp ` W )
  assume islshpat.p: |- .(+) = ( LSSum ` W )
  assume islshpat.h: |- H = ( LSHyp ` W )
  assume islshpat.a: |- A = ( LSAtoms ` W )
  assume islshpat.w: |- ( ph -> W e. LMod )

  disjoint .(+) q
  disjoint S q
  disjoint U q
  disjoint V q
  disjoint W q
  disjoint ph q
  disjoint q v
  disjoint .(+) v
  disjoint S v
  disjoint U v
  disjoint V v
  disjoint W v
  disjoint ph v
  assert |- ( ph -> ( U e. H <-> ( U e. S /\ U =/= V /\ E. q e. A ( U .(+) q ) = V ) ) )

  proof
    wph
    cU
    cH
    wcel
    cU
    cS
    wcel
    #
    cU
    cV
    wne
    #
    cU
    vv
    cv
    #
    csn
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    c.po
    co
    #
    cV
    wceq
    #
    vv
    cV
    wrex
    #
    w3a
    #
    @0
    @1
    cU
    vq
    cv
    #
    c.po
    co
    #
    cV
    wceq
    #
    vq
    cA
    wrex
    #
    w3a
    #
    wph
    vv
    c.po
    cS
    cU
    cH
    @4
    cV
    cW
    islshpat.v
    @4
    eqid
    #
    islshpat.s
    islshpat.p
    islshpat.h
    islshpat.w
    islshpsm
    wph
    @9
    @10
    cA
    wcel
    #
    @0
    @1
    wa
    #
    @12
    wa
    #
    wa
    #
    vq
    wex
    #
    @14
    @9
    @17
    @7
    wa
    #
    vv
    cV
    wrex
    #
    wph
    @20
    @9
    @17
    @8
    wa
    @22
    @0
    @1
    @8
    df-3an
    @17
    @7
    vv
    cV
    r19.42v
    bitr4i
    wph
    @22
    @10
    @5
    wceq
    #
    vv
    cV
    cW
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wrex
    #
    @18
    wa
    #
    vq
    wex
    #
    @20
    wph
    @22
    @23
    @21
    wa
    #
    vv
    @26
    wrex
    #
    vq
    wex
    #
    @29
    wph
    @22
    @2
    @26
    wcel
    #
    @21
    wa
    #
    vv
    wex
    #
    @32
    @22
    @2
    cV
    wcel
    #
    @21
    wa
    #
    vv
    wex
    wph
    @35
    @21
    vv
    cV
    df-rex
    wph
    @37
    @34
    vv
    wph
    @37
    @36
    @17
    @2
    @24
    wne
    #
    @7
    wa
    #
    wa
    #
    wa
    #
    @34
    wph
    @36
    @21
    @40
    wph
    @36
    wa
    #
    @17
    @7
    @39
    @42
    @17
    wa
    #
    @7
    @38
    @43
    @2
    @24
    @6
    cV
    @43
    @2
    @24
    wceq
    #
    @6
    cV
    wne
    @43
    @44
    wa
    #
    @6
    cU
    cV
    @45
    @6
    cU
    @25
    c.po
    co
    #
    cU
    @45
    @5
    @25
    cU
    c.po
    @45
    @5
    @25
    @4
    cfv
    #
    @25
    @45
    @3
    @25
    @4
    @45
    @2
    @24
    @43
    @44
    simpr
    sneqd
    fveq2d
    @45
    cW
    clmod
    wcel
    #
    @47
    @25
    wceq
    wph
    @48
    @36
    @17
    @44
    islshpat.w
    ad3antrrr
    #
    @4
    cW
    @24
    @24
    eqid
    #
    @15
    lspsn0
    syl
    eqtrd
    oveq2d
    @45
    cU
    cW
    csubg
    cfv
    wcel
    #
    @46
    cU
    wceq
    @45
    @48
    @0
    @51
    @49
    @42
    @0
    @1
    @44
    simplrl
    cS
    cU
    cW
    islshpat.s
    lsssubg
    syl2anc
    c.po
    cW
    cU
    @24
    @50
    islshpat.p
    lsm01
    syl
    eqtrd
    @42
    @0
    @1
    @44
    simplrr
    eqnetrd
    ex
    necon2d
    pm4.71rd
    pm5.32da
    pm5.32da
    @34
    @36
    @38
    wa
    #
    @21
    wa
    #
    @41
    @33
    @52
    @21
    @2
    cV
    @24
    eldifsn
    anbi1i
    @53
    @36
    @38
    @21
    wa
    #
    wa
    @41
    @36
    @38
    @21
    anass
    @54
    @40
    @36
    @38
    @17
    @7
    an12
    anbi2i
    bitri
    bitr2i
    syl6bb
    exbidv
    syl5bb
    @35
    @21
    @23
    wa
    #
    vv
    @26
    wrex
    #
    vq
    wex
    #
    @32
    @57
    @21
    vv
    @26
    wrex
    @35
    @21
    vq
    vv
    @26
    @5
    @3
    @4
    fvex
    rexcom4b
    @21
    vv
    @26
    df-rex
    bitr2i
    @56
    @31
    vq
    @55
    @30
    vv
    @26
    @21
    @23
    ancom
    rexbii
    exbii
    bitri
    syl6bb
    @28
    @31
    vq
    @28
    @23
    @18
    wa
    #
    vv
    @26
    wrex
    @31
    @23
    @18
    vv
    @26
    r19.41v
    @58
    @30
    vv
    @26
    @23
    @18
    @21
    @23
    @12
    @7
    @17
    @23
    @11
    @6
    cV
    @10
    @5
    cU
    c.po
    oveq2
    eqeq1d
    anbi2d
    pm5.32i
    rexbii
    bitr3i
    exbii
    syl6bbr
    wph
    @19
    @28
    vq
    wph
    @16
    @27
    @18
    wph
    @48
    @16
    @27
    wb
    islshpat.w
    vv
    cA
    @10
    @4
    cV
    cW
    clmod
    @24
    islshpat.v
    @15
    @50
    islshpat.a
    islsat
    syl
    anbi1d
    exbidv
    bitr4d
    syl5bb
    @14
    @17
    @13
    wa
    #
    @20
    @0
    @1
    @13
    df-3an
    @59
    @18
    vq
    cA
    wrex
    @20
    @17
    @12
    vq
    cA
    r19.42v
    @18
    vq
    cA
    df-rex
    bitr3i
    bitr2i
    syl6bb
    bitrd
end
