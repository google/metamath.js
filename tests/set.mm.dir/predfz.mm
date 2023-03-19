include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "cpred.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "cz.mm"
include "wb.mm"
include "elfzelz.mm"
include "zltlem1.mm"
include "syl2anr.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "peano2zm.mm"
include "syl.mm"
include "elfz5.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "vex.mm"
include "elpred.mm"
include "wss.mm"
include "caddc.mm"
include "elfzuz3.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "peano2uzr.mm"
include "syl2anc.mm"
include "fzss2.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem predfz
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( K e. ( M ... N ) -> Pred ( < , ( M ... N ) , K ) = ( M ... ( K - 1 ) ) )

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
    clt
    cK
    cpred
    #
    cM
    cK
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
    @0
    wcel
    #
    @5
    cK
    clt
    wbr
    #
    wa
    @6
    @5
    @4
    wcel
    #
    wa
    @5
    @2
    wcel
    @8
    @1
    @6
    @7
    @8
    @1
    @6
    wa
    @7
    @5
    @3
    cle
    wbr
    #
    @8
    @6
    @5
    cz
    wcel
    cK
    cz
    wcel
    #
    @7
    @9
    wb
    @1
    @5
    cM
    cN
    elfzelz
    cK
    cM
    cN
    elfzelz
    #
    @5
    cK
    zltlem1
    syl2anr
    @6
    @5
    cM
    cuz
    cfv
    wcel
    @3
    cz
    wcel
    #
    @8
    @9
    wb
    @1
    @5
    cM
    cN
    elfzuz
    @1
    @10
    @12
    @11
    cK
    peano2zm
    syl
    #
    @5
    cM
    @3
    elfz5
    syl2anr
    bitr4d
    pm5.32da
    @0
    @0
    clt
    cK
    @5
    vx
    vex
    elpred
    @1
    @8
    @6
    @1
    @4
    @0
    @5
    @1
    cN
    @3
    cuz
    cfv
    wcel
    #
    @4
    @0
    wss
    @1
    @12
    cN
    @3
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @14
    @13
    @1
    cN
    cK
    cuz
    cfv
    @16
    cK
    cM
    cN
    elfzuz3
    @1
    @15
    cK
    cuz
    @1
    cK
    cc
    wcel
    c1
    cc
    wcel
    @15
    cK
    wceq
    @1
    cK
    @11
    zcnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    fveq2d
    eleqtrrd
    @3
    cN
    peano2uzr
    syl2anc
    @3
    cM
    cN
    fzss2
    syl
    sseld
    pm4.71rd
    3bitr4d
    eqrdv
end
