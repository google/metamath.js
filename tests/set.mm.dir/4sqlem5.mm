include "cz.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "zcnd.mm"
include "c2.mm"
include "caddc.mm"
include "cmo.mm"
include "cc.mm"
include "zred.mm"
include "nnred.mm"
include "rehalfcld.mm"
include "readdcld.mm"
include "nnrpd.mm"
include "modcld.mm"
include "recnd.mm"
include "subcld.mm"
include "syl5eqel.mm"
include "nncand.mm"
include "cmul.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "oveq2i.mm"
include "subsub3d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "moddifz.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "eqeltrrd.mm"
include "zsubcld.mm"
include "jca.mm"

theorem 4sqlem5
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  assume 4sqlem5.2: |- ( ph -> A e. ZZ )
  assume 4sqlem5.3: |- ( ph -> M e. NN )
  assume 4sqlem5.4: |- B = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )


  assert |- ( ph -> ( B e. ZZ /\ ( ( A - B ) / M ) e. ZZ ) )

  proof
    wph
    cB
    cz
    wcel
    cA
    cB
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cz
    wcel
    wph
    cA
    @0
    cmin
    co
    cB
    cz
    wph
    cA
    cB
    wph
    cA
    4sqlem5.2
    zcnd
    #
    wph
    cB
    cA
    cM
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cM
    cmo
    co
    #
    @3
    cmin
    co
    #
    cc
    4sqlem5.4
    wph
    @5
    @3
    wph
    @5
    wph
    @4
    cM
    wph
    cA
    @3
    wph
    cA
    4sqlem5.2
    zred
    wph
    cM
    wph
    cM
    4sqlem5.3
    nnred
    #
    rehalfcld
    #
    readdcld
    #
    wph
    cM
    4sqlem5.3
    nnrpd
    #
    modcld
    recnd
    #
    wph
    @3
    @8
    recnd
    #
    subcld
    syl5eqel
    #
    nncand
    wph
    cA
    @0
    4sqlem5.2
    wph
    @1
    cM
    cmul
    co
    @0
    cz
    wph
    @0
    cM
    wph
    cA
    cB
    @2
    @13
    subcld
    wph
    cM
    @7
    recnd
    wph
    cM
    4sqlem5.3
    nnne0d
    divcan1d
    wph
    @1
    cM
    wph
    @1
    @4
    @5
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cz
    wph
    @0
    @14
    cM
    cdiv
    wph
    @0
    cA
    @6
    cmin
    co
    @14
    cB
    @6
    cA
    cmin
    4sqlem5.4
    oveq2i
    wph
    cA
    @5
    @3
    @2
    @11
    @12
    subsub3d
    syl5eq
    oveq1d
    wph
    @4
    cr
    wcel
    cM
    crp
    wcel
    @15
    cz
    wcel
    @9
    @10
    @4
    cM
    moddifz
    syl2anc
    eqeltrd
    #
    wph
    cM
    4sqlem5.3
    nnzd
    zmulcld
    eqeltrrd
    zsubcld
    eqeltrrd
    @16
    jca
end
