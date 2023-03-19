include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "clt.mm"
include "cpred.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cz.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "vex.mm"
include "elpred.mm"
include "wb.mm"
include "eluzelz.mm"
include "zltlem1.mm"
include "syl2anr.mm"
include "pm5.32da.mm"
include "eluzel2.mm"
include "eluz1.mm"
include "syl.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "peano2zm.mm"
include "jca.mm"
include "biantrurd.mm"
include "w3a.mm"
include "elfz2.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "anass.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem preduz
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` M ) -> Pred ( < , ( ZZ>= ` M ) , N ) = ( M ... ( N - 1 ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    vx
    @0
    clt
    cN
    cpred
    #
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @1
    vx
    cv
    #
    @2
    wcel
    #
    cM
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    wa
    #
    @5
    cz
    wcel
    #
    cM
    @5
    cle
    wbr
    #
    wa
    #
    @5
    @3
    cle
    wbr
    #
    wa
    #
    wa
    #
    @5
    @4
    wcel
    #
    @1
    @6
    @14
    @15
    @1
    @6
    @5
    @0
    wcel
    #
    @5
    cN
    clt
    wbr
    #
    wa
    #
    @14
    @0
    @0
    clt
    cN
    @5
    vx
    vex
    elpred
    @1
    @19
    @17
    @13
    wa
    @14
    @1
    @17
    @18
    @13
    @17
    @10
    cN
    cz
    wcel
    #
    @18
    @13
    wb
    @1
    cM
    @5
    eluzelz
    cM
    cN
    eluzelz
    #
    @5
    cN
    zltlem1
    syl2anr
    pm5.32da
    @1
    @17
    @12
    @13
    @1
    @7
    @17
    @12
    wb
    cM
    cN
    eluzel2
    #
    cM
    @5
    eluz1
    syl
    anbi1d
    bitrd
    bitrd
    @1
    @9
    @14
    @1
    @7
    @8
    @22
    @1
    @20
    @8
    @21
    cN
    peano2zm
    syl
    jca
    biantrurd
    bitrd
    @16
    @7
    @8
    @10
    w3a
    #
    @11
    @13
    wa
    #
    wa
    @9
    @10
    wa
    #
    @24
    wa
    #
    @15
    @5
    cM
    @3
    elfz2
    @23
    @25
    @24
    @7
    @8
    @10
    df-3an
    anbi1i
    @26
    @9
    @10
    @24
    wa
    #
    wa
    @15
    @9
    @10
    @24
    anass
    @14
    @27
    @9
    @10
    @11
    @13
    anass
    anbi2i
    bitr4i
    3bitri
    syl6bbr
    eqrdv
end
