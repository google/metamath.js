include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "w3a.mm"
include "co.mm"
include "clmod.mm"
include "wb.mm"
include "islshp.mm"
include "syl.mm"
include "wa.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "lspid.mm"
include "syl2anc.mm"
include "uneq1d.mm"
include "fveq2d.mm"
include "wss.mm"
include "lssss.mm"
include "snssi.mm"
include "adantl.mm"
include "lspun.mm"
include "syl3anc.mm"
include "lspcl.mm"
include "lsmsp.mm"
include "3eqtr4rd.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "pm5.32da.mm"
include "bicomd.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem islshpsm
  let wph: wff ph
  let vv: setvar v
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  assume islshpsm.v: |- V = ( Base ` W )
  assume islshpsm.n: |- N = ( LSpan ` W )
  assume islshpsm.s: |- S = ( LSubSp ` W )
  assume islshpsm.p: |- .(+) = ( LSSum ` W )
  assume islshpsm.h: |- H = ( LSHyp ` W )
  assume islshpsm.w: |- ( ph -> W e. LMod )

  disjoint S v
  disjoint U v
  disjoint V v
  disjoint W v
  disjoint ph v
  assert |- ( ph -> ( U e. H <-> ( U e. S /\ U =/= V /\ E. v e. V ( U .(+) ( N ` { v } ) ) = V ) ) )

  proof
    wph
    cU
    cH
    wcel
    #
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
    cun
    cN
    cfv
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
    @1
    @2
    cU
    @4
    cN
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
    wph
    cW
    clmod
    wcel
    #
    @0
    @8
    wb
    islshpsm.w
    vv
    cS
    cU
    cH
    cN
    cV
    cW
    clmod
    islshpsm.v
    islshpsm.n
    islshpsm.s
    islshpsm.h
    islshp
    syl
    wph
    @1
    @2
    wa
    #
    @7
    wa
    #
    @15
    @12
    wa
    #
    @8
    @13
    wph
    @17
    @16
    wph
    @15
    @12
    @7
    wph
    @15
    wa
    #
    @11
    @6
    vv
    cV
    @18
    @3
    cV
    wcel
    #
    wa
    #
    @10
    @5
    cV
    @20
    cU
    cN
    cfv
    #
    @9
    cun
    #
    cN
    cfv
    #
    cU
    @9
    cun
    #
    cN
    cfv
    #
    @5
    @10
    @20
    @22
    @24
    cN
    @20
    @21
    cU
    @9
    @20
    @14
    @1
    @21
    cU
    wceq
    wph
    @14
    @15
    @19
    islshpsm.w
    ad2antrr
    #
    wph
    @1
    @2
    @19
    simplrl
    #
    cS
    cU
    cN
    cW
    islshpsm.s
    islshpsm.n
    lspid
    syl2anc
    uneq1d
    fveq2d
    @20
    @14
    cU
    cV
    wss
    #
    @4
    cV
    wss
    #
    @5
    @23
    wceq
    @26
    @20
    @1
    @28
    @27
    cS
    cU
    cV
    cW
    islshpsm.v
    islshpsm.s
    lssss
    syl
    @19
    @29
    @18
    @3
    cV
    snssi
    adantl
    #
    cU
    @4
    cN
    cV
    cW
    islshpsm.v
    islshpsm.n
    lspun
    syl3anc
    @20
    @14
    @1
    @9
    cS
    wcel
    #
    @10
    @25
    wceq
    @26
    @27
    @20
    @14
    @29
    @31
    @26
    @30
    cS
    @4
    cN
    cV
    cW
    islshpsm.v
    islshpsm.s
    islshpsm.n
    lspcl
    syl2anc
    c.po
    cS
    cU
    @9
    cN
    cW
    islshpsm.s
    islshpsm.n
    islshpsm.p
    lsmsp
    syl3anc
    3eqtr4rd
    eqeq1d
    rexbidva
    pm5.32da
    bicomd
    @1
    @2
    @7
    df-3an
    @1
    @2
    @12
    df-3an
    3bitr4g
    bitrd
end
