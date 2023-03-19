include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "ccxp.mm"
include "clogb.mm"
include "cfl.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "crp.mm"
include "relogbzcl.mm"
include "syl2anc.mm"
include "flle.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "cz.mm"
include "eluzelz.mm"
include "zred.mm"
include "eluz2b1.mm"
include "simprbi.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "cxpled.mm"
include "mpbid.mm"
include "zcnd.mm"
include "cn.mm"
include "eluz2nn.mm"
include "nnne0d.mm"
include "cxpexpzd.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "wceq.mm"
include "eluz2cnn0n1.mm"
include "wne.mm"
include "wa.mm"
include "rpcnne0.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "cxplogb.mm"
include "3brtr3d.mm"
include "flltp1.mm"
include "a1i.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "peano2zd.mm"
include "cxpltd.mm"
include "jca.mm"

theorem fllogbd
  let wph: wff ph
  let cB: class B
  let cE: class E
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fllogbd.b: |- ( ph -> B e. ( ZZ>= ` 2 ) )
  assume fllogbd.x: |- ( ph -> X e. RR+ )
  assume fllogbd.e: |- E = ( |_ ` ( B logb X ) )


  assert |- ( ph -> ( ( B ^ E ) <_ X /\ X < ( B ^ ( E + 1 ) ) ) )

  proof
    wph
    cB
    cE
    cexp
    co
    #
    cX
    cle
    wbr
    cX
    cB
    cE
    c1
    caddc
    co
    #
    cexp
    co
    #
    clt
    wbr
    wph
    cB
    cE
    ccxp
    co
    #
    cB
    cB
    cX
    clogb
    co
    #
    ccxp
    co
    #
    @0
    cX
    cle
    wph
    cE
    @4
    cle
    wbr
    @3
    @5
    cle
    wbr
    wph
    cE
    @4
    cfl
    cfv
    #
    @4
    cle
    fllogbd.e
    wph
    @4
    cr
    wcel
    #
    @6
    @4
    cle
    wbr
    wph
    cB
    c2
    cuz
    cfv
    wcel
    #
    cX
    crp
    wcel
    #
    @7
    fllogbd.b
    fllogbd.x
    cB
    cX
    relogbzcl
    syl2anc
    #
    @4
    flle
    syl
    syl5eqbr
    wph
    cB
    cE
    @4
    wph
    cB
    wph
    @8
    cB
    cz
    wcel
    #
    fllogbd.b
    c2
    cB
    eluzelz
    syl
    #
    zred
    #
    wph
    @8
    c1
    cB
    clt
    wbr
    #
    fllogbd.b
    @8
    @11
    @14
    cB
    eluz2b1
    simprbi
    syl
    #
    wph
    cE
    wph
    cE
    @6
    cz
    fllogbd.e
    wph
    @4
    @10
    flcld
    syl5eqel
    #
    zred
    @10
    cxpled
    mpbid
    wph
    cB
    cE
    wph
    cB
    @12
    zcnd
    #
    wph
    cB
    wph
    @8
    cB
    cn
    wcel
    fllogbd.b
    cB
    eluz2nn
    syl
    nnne0d
    #
    @16
    cxpexpzd
    wph
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cX
    cc
    cc0
    csn
    cdif
    wcel
    #
    @5
    cX
    wceq
    wph
    @8
    @19
    fllogbd.b
    cB
    eluz2cnn0n1
    syl
    wph
    @9
    @20
    fllogbd.x
    @9
    cX
    cc
    wcel
    cX
    cc0
    wne
    wa
    @20
    cX
    rpcnne0
    cX
    cc
    cc0
    eldifsn
    sylibr
    syl
    cB
    cX
    cxplogb
    syl2anc
    #
    3brtr3d
    wph
    @5
    cB
    @1
    ccxp
    co
    #
    cX
    @2
    clt
    wph
    @4
    @1
    clt
    wbr
    @5
    @22
    clt
    wbr
    wph
    @4
    @6
    c1
    caddc
    co
    #
    @1
    clt
    wph
    @7
    @4
    @23
    clt
    wbr
    @10
    @4
    flltp1
    syl
    wph
    cE
    @6
    c1
    caddc
    cE
    @6
    wceq
    wph
    fllogbd.e
    a1i
    oveq1d
    breqtrrd
    wph
    cB
    @4
    @1
    @13
    @15
    @10
    wph
    @1
    wph
    cE
    @16
    peano2zd
    #
    zred
    cxpltd
    mpbid
    @21
    wph
    cB
    @1
    @17
    @18
    @24
    cxpexpzd
    3brtr3d
    jca
end
