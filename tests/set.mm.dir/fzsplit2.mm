include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "elfzelz.mm"
include "zred.mm"
include "cz.mm"
include "eluzel2.mm"
include "adantl.mm"
include "lelttric.mm"
include "syl2anr.mm"
include "wb.mm"
include "elfzuz.mm"
include "elfz5.mm"
include "simpl.mm"
include "eluzelz.mm"
include "syl.mm"
include "eluz.mm"
include "syl2an.mm"
include "elfzuz3.mm"
include "elfzuzb.mm"
include "rbaib.mm"
include "zltp1le.mm"
include "3bitr4d.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "simpr.mm"
include "uztrn.mm"
include "sylanbrc.mm"
include "jaodan.mm"
include "impbida.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem fzsplit2
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( ( K + 1 ) e. ( ZZ>= ` M ) /\ N e. ( ZZ>= ` K ) ) -> ( M ... N ) = ( ( M ... K ) u. ( ( K + 1 ) ... N ) ) )

  proof
    cK
    c1
    caddc
    co
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cK
    cuz
    cfv
    wcel
    #
    wa
    #
    vx
    cM
    cN
    cfz
    co
    #
    cM
    cK
    cfz
    co
    #
    @0
    cN
    cfz
    co
    #
    cun
    #
    @4
    vx
    cv
    #
    @5
    wcel
    #
    @9
    @6
    wcel
    #
    @9
    @7
    wcel
    #
    wo
    #
    @9
    @8
    wcel
    @4
    @10
    @13
    @4
    @10
    wa
    #
    @13
    @9
    cK
    cle
    wbr
    #
    cK
    @9
    clt
    wbr
    #
    wo
    #
    @10
    @9
    cr
    wcel
    cK
    cr
    wcel
    @17
    @4
    @10
    @9
    @9
    cM
    cN
    elfzelz
    #
    zred
    @4
    cK
    @3
    cK
    cz
    wcel
    #
    @2
    cK
    cN
    eluzel2
    adantl
    #
    zred
    @9
    cK
    lelttric
    syl2anr
    @14
    @11
    @15
    @12
    @16
    @10
    @9
    @1
    wcel
    #
    @19
    @11
    @15
    wb
    @4
    @9
    cM
    cN
    elfzuz
    @20
    @9
    cM
    cK
    elfz5
    syl2anr
    @14
    @9
    @0
    cuz
    cfv
    wcel
    #
    @0
    @9
    cle
    wbr
    #
    @12
    @16
    @4
    @0
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @22
    @23
    wb
    @10
    @4
    @2
    @24
    @2
    @3
    simpl
    #
    cM
    @0
    eluzelz
    syl
    @18
    @0
    @9
    eluz
    syl2an
    @14
    cN
    @9
    cuz
    cfv
    #
    wcel
    #
    @12
    @22
    wb
    @10
    @28
    @4
    @9
    cM
    cN
    elfzuz3
    adantl
    @12
    @22
    @28
    @9
    @0
    cN
    elfzuzb
    rbaib
    syl
    @4
    @19
    @25
    @16
    @23
    wb
    @10
    @20
    @18
    cK
    @9
    zltp1le
    syl2an
    3bitr4d
    orbi12d
    mpbird
    @4
    @11
    @10
    @12
    @4
    @11
    wa
    @21
    @28
    @10
    @11
    @21
    @4
    @9
    cM
    cK
    elfzuz
    adantl
    @4
    @3
    cK
    @27
    wcel
    @28
    @11
    @2
    @3
    simpr
    @9
    cM
    cK
    elfzuz3
    cK
    cN
    @9
    uztrn
    syl2an
    @9
    cM
    cN
    elfzuzb
    #
    sylanbrc
    @4
    @12
    wa
    @21
    @28
    @10
    @12
    @22
    @2
    @21
    @4
    @9
    @0
    cN
    elfzuz
    @26
    @0
    @9
    cM
    uztrn
    syl2anr
    @12
    @28
    @4
    @9
    @0
    cN
    elfzuz3
    adantl
    @29
    sylanbrc
    jaodan
    impbida
    @9
    @6
    @7
    elun
    syl6bbr
    eqrdv
end
