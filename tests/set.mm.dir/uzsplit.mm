include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "eluzelre.mm"
include "lelttric.mm"
include "syl2an.mm"
include "cz.mm"
include "wb.mm"
include "eluzelz.mm"
include "eluz.mm"
include "eluzel2.mm"
include "w3a.mm"
include "elfzm11.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "syl2anr.mm"
include "eluzle.mm"
include "jca.mm"
include "adantl.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "orcomd.mm"
include "ex.mm"
include "wi.mm"
include "elfzuz.mm"
include "a1i.mm"
include "uztrn.mm"
include "expcom.mm"
include "jaod.mm"
include "impbid.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem uzsplit
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( N e. ( ZZ>= ` M ) -> ( ZZ>= ` M ) = ( ( M ... ( N - 1 ) ) u. ( ZZ>= ` N ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    vk
    @0
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cN
    cuz
    cfv
    #
    cun
    #
    @1
    vk
    cv
    #
    @0
    wcel
    #
    @6
    @3
    wcel
    #
    @6
    @4
    wcel
    #
    wo
    #
    @6
    @5
    wcel
    @1
    @7
    @10
    @1
    @7
    @10
    @1
    @7
    wa
    #
    @9
    @8
    @11
    @9
    @8
    wo
    cN
    @6
    cle
    wbr
    #
    @6
    cN
    clt
    wbr
    #
    wo
    #
    @1
    cN
    cr
    wcel
    @6
    cr
    wcel
    @14
    @7
    cM
    cN
    eluzelre
    cM
    @6
    eluzelre
    cN
    @6
    lelttric
    syl2an
    @11
    @9
    @12
    @8
    @13
    @1
    cN
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @9
    @12
    wb
    @7
    cM
    cN
    eluzelz
    #
    cM
    @6
    eluzelz
    #
    cN
    @6
    eluz
    syl2an
    @11
    @8
    @16
    cM
    @6
    cle
    wbr
    #
    wa
    #
    @13
    wa
    #
    @13
    @7
    cM
    cz
    wcel
    #
    @15
    @8
    @21
    wb
    @1
    cM
    @6
    eluzel2
    @17
    @22
    @15
    wa
    @8
    @16
    @19
    @13
    w3a
    @21
    @6
    cM
    cN
    elfzm11
    @16
    @19
    @13
    df-3an
    syl6bb
    syl2anr
    @11
    @20
    @13
    @7
    @20
    @1
    @7
    @16
    @19
    @18
    cM
    @6
    eluzle
    jca
    adantl
    biantrurd
    bitr4d
    orbi12d
    mpbird
    orcomd
    ex
    @1
    @8
    @7
    @9
    @8
    @7
    wi
    @1
    @6
    cM
    @2
    elfzuz
    a1i
    @9
    @1
    @7
    cN
    @6
    cM
    uztrn
    expcom
    jaod
    impbid
    @6
    @3
    @4
    elun
    syl6bbr
    eqrdv
end
