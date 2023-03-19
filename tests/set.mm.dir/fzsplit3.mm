include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "1red.mm"
include "resubcld.mm"
include "lelttric.mm"
include "syl2anr.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "wb.mm"
include "elfzuz.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "elfz5.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "elfzuzb.mm"
include "rbaib.mm"
include "syl.mm"
include "eluz.mm"
include "syl2an.mm"
include "zlem1lt.mm"
include "3bitrd.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "adantr.mm"
include "caddc.mm"
include "peano2uz.mm"
include "recnd.mm"
include "npcand.mm"
include "eleq1d.mm"
include "mpbid.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "jaodan.mm"
include "impbida.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem fzsplit3
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( K e. ( M ... N ) -> ( M ... N ) = ( ( M ... ( K - 1 ) ) u. ( K ... N ) ) )

  proof
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    vx
    @0
    cM
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    cK
    cN
    cfz
    co
    #
    cun
    #
    @1
    vx
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
    wa
    #
    @10
    @6
    @2
    cle
    wbr
    #
    @2
    @6
    clt
    wbr
    #
    wo
    #
    @7
    @6
    cr
    wcel
    @2
    cr
    wcel
    @14
    @1
    @7
    @6
    @6
    cM
    cN
    elfzelz
    #
    zred
    @1
    cK
    c1
    @1
    cK
    cK
    cM
    cN
    elfzelz
    #
    zred
    #
    @1
    1red
    #
    resubcld
    @6
    @2
    lelttric
    syl2anr
    @11
    @8
    @12
    @9
    @13
    @7
    @6
    cM
    cuz
    cfv
    #
    wcel
    #
    @2
    cz
    wcel
    @8
    @12
    wb
    @1
    @6
    cM
    cN
    elfzuz
    @1
    cK
    c1
    @16
    @1
    1zzd
    zsubcld
    @6
    cM
    @2
    elfz5
    syl2anr
    @11
    @9
    @6
    cK
    cuz
    cfv
    #
    wcel
    #
    cK
    @6
    cle
    wbr
    #
    @13
    @11
    cN
    @6
    cuz
    cfv
    #
    wcel
    #
    @9
    @22
    wb
    @7
    @25
    @1
    @6
    cM
    cN
    elfzuz3
    adantl
    @9
    @22
    @25
    @6
    cK
    cN
    elfzuzb
    rbaib
    syl
    @1
    cK
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @22
    @23
    wb
    @7
    @16
    @15
    cK
    @6
    eluz
    syl2an
    @1
    @26
    @27
    @23
    @13
    wb
    @7
    @16
    @15
    cK
    @6
    zlem1lt
    syl2an
    3bitrd
    orbi12d
    mpbird
    @1
    @8
    @7
    @9
    @1
    @8
    wa
    #
    @20
    @25
    @7
    @8
    @20
    @1
    @6
    cM
    @2
    elfzuz
    adantl
    @28
    cN
    @21
    wcel
    #
    cK
    @24
    wcel
    #
    @25
    @1
    @29
    @8
    cK
    cM
    cN
    elfzuz3
    adantr
    @28
    @2
    c1
    caddc
    co
    #
    @24
    wcel
    #
    @30
    @28
    @2
    @24
    wcel
    #
    @32
    @8
    @33
    @1
    @6
    cM
    @2
    elfzuz3
    adantl
    @6
    @2
    peano2uz
    syl
    @1
    @32
    @30
    wb
    @8
    @1
    @31
    cK
    @24
    @1
    cK
    c1
    @1
    cK
    @17
    recnd
    @1
    c1
    @18
    recnd
    npcand
    eleq1d
    adantr
    mpbid
    cK
    cN
    @6
    uztrn
    syl2anc
    @6
    cM
    cN
    elfzuzb
    #
    sylanbrc
    @1
    @9
    wa
    @20
    @25
    @7
    @9
    @22
    cK
    @19
    wcel
    @20
    @1
    @6
    cK
    cN
    elfzuz
    cK
    cM
    cN
    elfzuz
    cK
    @6
    cM
    uztrn
    syl2anr
    @9
    @25
    @1
    @6
    cK
    cN
    elfzuz3
    adantl
    @34
    sylanbrc
    jaodan
    impbida
    @6
    @3
    @4
    elun
    syl6bbr
    eqrdv
end
