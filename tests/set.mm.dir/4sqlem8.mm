include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "4sqlem5.mm"
include "simprd.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "simpld.mm"
include "zsubcld.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "caddc.mm"
include "cmul.mm"
include "zaddcld.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "subsq.mm"
include "breqtrrd.mm"
include "wa.mm"
include "wi.mm"
include "zsqcl.mm"
include "syl.mm"
include "dvdstr.mm"
include "mp2and.mm"

theorem 4sqlem8
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  assume 4sqlem5.2: |- ( ph -> A e. ZZ )
  assume 4sqlem5.3: |- ( ph -> M e. NN )
  assume 4sqlem5.4: |- B = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )


  assert |- ( ph -> M || ( ( A ^ 2 ) - ( B ^ 2 ) ) )

  proof
    wph
    cM
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    @0
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    cM
    @4
    cdvds
    wbr
    #
    wph
    @1
    @0
    cM
    cdiv
    co
    cz
    wcel
    #
    wph
    cB
    cz
    wcel
    #
    @7
    wph
    cA
    cB
    cM
    4sqlem5.2
    4sqlem5.3
    4sqlem5.4
    4sqlem5
    #
    simprd
    wph
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    @0
    cz
    wcel
    #
    @1
    @7
    wb
    wph
    cM
    4sqlem5.3
    nnzd
    #
    wph
    cM
    4sqlem5.3
    nnne0d
    wph
    cA
    cB
    4sqlem5.2
    wph
    @8
    @7
    @9
    simpld
    #
    zsubcld
    #
    cM
    @0
    dvdsval2
    syl3anc
    mpbird
    wph
    @0
    cA
    cB
    caddc
    co
    #
    @0
    cmul
    co
    #
    @4
    cdvds
    wph
    @15
    cz
    wcel
    @11
    @0
    @16
    cdvds
    wbr
    wph
    cA
    cB
    4sqlem5.2
    @13
    zaddcld
    @14
    @15
    @0
    dvdsmul2
    syl2anc
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    @4
    @16
    wceq
    wph
    cA
    4sqlem5.2
    zcnd
    wph
    cB
    @13
    zcnd
    cA
    cB
    subsq
    syl2anc
    breqtrrd
    wph
    @10
    @11
    @4
    cz
    wcel
    @1
    @5
    wa
    @6
    wi
    @12
    @14
    wph
    @2
    @3
    wph
    cA
    cz
    wcel
    @2
    cz
    wcel
    4sqlem5.2
    cA
    zsqcl
    syl
    wph
    @8
    @3
    cz
    wcel
    @13
    cB
    zsqcl
    syl
    zsubcld
    cM
    @0
    @4
    dvdstr
    syl3anc
    mp2and
end
