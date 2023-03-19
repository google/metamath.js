include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cz.mm"
include "wcel.mm"
include "cmin.mm"
include "4sqlem5.mm"
include "simpld.mm"
include "zred.mm"
include "nnrpd.mm"
include "rphalfcld.mm"
include "rpred.mm"
include "clt.mm"
include "4sqlem6.mm"
include "simprd.mm"
include "ltled.mm"
include "lenegcon1d.mm"
include "cr.mm"
include "cc0.mm"
include "wa.mm"
include "wb.mm"
include "rpge0d.mm"
include "lenegsq.mm"
include "syl3anc.mm"
include "mpbi2and.mm"
include "cmul.mm"
include "2cnd.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "nncnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "sqdivd.mm"
include "sqcld.mm"
include "divdiv1d.mm"
include "3eqtr4d.mm"
include "breqtrd.mm"

theorem 4sqlem7
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  assume 4sqlem5.2: |- ( ph -> A e. ZZ )
  assume 4sqlem5.3: |- ( ph -> M e. NN )
  assume 4sqlem5.4: |- B = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )


  assert |- ( ph -> ( B ^ 2 ) <_ ( ( ( M ^ 2 ) / 2 ) / 2 ) )

  proof
    wph
    cB
    c2
    cexp
    co
    #
    cM
    c2
    cdiv
    co
    #
    c2
    cexp
    co
    #
    cM
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    c2
    cdiv
    co
    #
    cle
    wph
    cB
    @1
    cle
    wbr
    #
    cB
    cneg
    @1
    cle
    wbr
    #
    @0
    @2
    cle
    wbr
    #
    wph
    cB
    @1
    wph
    cB
    wph
    cB
    cz
    wcel
    cA
    cB
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cA
    cB
    cM
    4sqlem5.2
    4sqlem5.3
    4sqlem5.4
    4sqlem5
    simpld
    zred
    #
    wph
    @1
    wph
    cM
    wph
    cM
    4sqlem5.3
    nnrpd
    rphalfcld
    #
    rpred
    #
    wph
    @1
    cneg
    cB
    cle
    wbr
    #
    cB
    @1
    clt
    wbr
    #
    wph
    cA
    cB
    cM
    4sqlem5.2
    4sqlem5.3
    4sqlem5.4
    4sqlem6
    #
    simprd
    ltled
    wph
    @1
    cB
    @10
    @8
    wph
    @11
    @12
    @13
    simpld
    lenegcon1d
    wph
    cB
    cr
    wcel
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @5
    @6
    wa
    @7
    wb
    @8
    @10
    wph
    @1
    @9
    rpge0d
    cB
    @1
    lenegsq
    syl3anc
    mpbi2and
    wph
    @3
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    @3
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @2
    @4
    wph
    @14
    @15
    @3
    cdiv
    wph
    c2
    wph
    2cnd
    #
    sqvald
    oveq2d
    wph
    cM
    c2
    wph
    cM
    4sqlem5.3
    nncnd
    #
    @16
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    sqdivd
    wph
    @3
    c2
    c2
    wph
    cM
    @17
    sqcld
    @16
    @16
    @18
    @18
    divdiv1d
    3eqtr4d
    breqtrd
end
