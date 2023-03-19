include "cc.mm"
include "wcel.mm"
include "cacos.mm"
include "cfv.mm"
include "cre.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "casin.mm"
include "cmin.mm"
include "cc0.mm"
include "cicc.mm"
include "acosval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "halfpire.mm"
include "recni.mm"
include "asincl.mm"
include "resub.mm"
include "sylancr.mm"
include "cr.mm"
include "rere.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "cle.mm"
include "wbr.mm"
include "recld.mm"
include "resubcl.mm"
include "cneg.mm"
include "w3a.mm"
include "asinbnd.mm"
include "neghalfpire.mm"
include "elicc2i.mm"
include "sylib.mm"
include "simp3d.mm"
include "wb.mm"
include "subge0.mm"
include "mpbird.mm"
include "a1i.mm"
include "pire.mm"
include "caddc.mm"
include "negsubi.mm"
include "pidiv2halves.mm"
include "subaddrii.mm"
include "eqtri.mm"
include "simp2d.mm"
include "syl5eqbr.mm"
include "subled.mm"
include "0re.mm"
include "syl3anbrc.mm"
include "eqeltrd.mm"

theorem acosbnd
  let cA: class A


  assert |- ( A e. CC -> ( Re ` ( arccos ` A ) ) e. ( 0 [,] _pi ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cacos
    cfv
    #
    cre
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cA
    casin
    cfv
    #
    cre
    cfv
    #
    cmin
    co
    #
    cc0
    cpi
    cicc
    co
    #
    @0
    @2
    @3
    @4
    cmin
    co
    #
    cre
    cfv
    #
    @6
    @0
    @1
    @8
    cre
    cA
    acosval
    fveq2d
    @0
    @9
    @3
    cre
    cfv
    #
    @5
    cmin
    co
    #
    @6
    @0
    @3
    cc
    wcel
    @4
    cc
    wcel
    @9
    @11
    wceq
    @3
    halfpire
    recni
    #
    cA
    asincl
    #
    @3
    @4
    resub
    sylancr
    @10
    @3
    @5
    cmin
    @3
    cr
    wcel
    #
    @10
    @3
    wceq
    halfpire
    @3
    rere
    ax-mp
    oveq1i
    syl6eq
    eqtrd
    @0
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cpi
    cle
    wbr
    @6
    @7
    wcel
    @0
    @14
    @5
    cr
    wcel
    #
    @15
    halfpire
    @0
    @4
    @13
    recld
    #
    @3
    @5
    resubcl
    sylancr
    @0
    @16
    @5
    @3
    cle
    wbr
    #
    @0
    @17
    @3
    cneg
    #
    @5
    cle
    wbr
    #
    @19
    @0
    @5
    @20
    @3
    cicc
    co
    wcel
    @17
    @21
    @19
    w3a
    cA
    asinbnd
    @20
    @3
    @5
    neghalfpire
    halfpire
    elicc2i
    sylib
    #
    simp3d
    @0
    @14
    @17
    @16
    @19
    wb
    halfpire
    @18
    @3
    @5
    subge0
    sylancr
    mpbird
    @0
    @3
    cpi
    @5
    @14
    @0
    halfpire
    a1i
    cpi
    cr
    wcel
    @0
    pire
    a1i
    @18
    @0
    @3
    cpi
    cmin
    co
    @20
    @5
    cle
    @3
    cpi
    @20
    @12
    cpi
    pire
    recni
    #
    @20
    neghalfpire
    recni
    cpi
    @20
    caddc
    co
    cpi
    @3
    cmin
    co
    @3
    cpi
    @3
    @23
    @12
    negsubi
    cpi
    @3
    @3
    @23
    @12
    @12
    pidiv2halves
    subaddrii
    eqtri
    subaddrii
    @0
    @17
    @21
    @19
    @22
    simp2d
    syl5eqbr
    subled
    cc0
    cpi
    @6
    0re
    pire
    elicc2i
    syl3anbrc
    eqeltrd
end
