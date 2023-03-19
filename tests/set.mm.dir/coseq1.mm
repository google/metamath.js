include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cc0.mm"
include "cpi.mm"
include "cz.mm"
include "cmul.mm"
include "cexp.mm"
include "cmin.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan2.mm"
include "mp3an23.mm"
include "fveq2d.mm"
include "halfcl.mm"
include "cos2tsin.mm"
include "syl.mm"
include "eqtr3d.mm"
include "eqeq1d.mm"
include "wb.mm"
include "sincld.mm"
include "sqcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "subsub23.mm"
include "mp3an13.mm"
include "eqcom.mm"
include "1m1e0.mm"
include "eqeq2i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "bitrd.mm"
include "wo.mm"
include "mul0or.mm"
include "wn.mm"
include "neii.mm"
include "biorf.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "sqeq0.mm"
include "3bitrd.mm"
include "sineq0.mm"
include "wa.mm"
include "pm3.2i.mm"
include "picn.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divdiv1.mm"
include "eleq1d.mm"

theorem coseq1
  let cA: class A


  assert |- ( A e. CC -> ( ( cos ` A ) = 1 <-> ( A / ( 2 x. _pi ) ) e. ZZ ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    c1
    wceq
    #
    cA
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cc0
    wceq
    #
    @3
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    c2
    cpi
    cmul
    co
    cdiv
    co
    #
    cz
    wcel
    @0
    @2
    c2
    @4
    c2
    cexp
    co
    #
    cmul
    co
    #
    cc0
    wceq
    #
    @9
    cc0
    wceq
    #
    @5
    @0
    @2
    c1
    @10
    cmin
    co
    #
    c1
    wceq
    #
    @11
    @0
    @1
    @13
    c1
    @0
    c2
    @3
    cmul
    co
    #
    ccos
    cfv
    #
    @1
    @13
    @0
    @15
    cA
    ccos
    @0
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @15
    cA
    wceq
    2cn
    2ne0
    cA
    c2
    divcan2
    mp3an23
    fveq2d
    @0
    @3
    cc
    wcel
    #
    @16
    @13
    wceq
    cA
    halfcl
    #
    @3
    cos2tsin
    syl
    eqtr3d
    eqeq1d
    @0
    @14
    c1
    c1
    cmin
    co
    #
    @10
    wceq
    #
    @11
    @0
    @10
    cc
    wcel
    #
    @14
    @22
    wb
    #
    @0
    @17
    @9
    cc
    wcel
    #
    @23
    2cn
    @0
    @4
    @0
    @3
    @20
    sincld
    #
    sqcld
    #
    c2
    @9
    mulcl
    sylancr
    c1
    cc
    wcel
    #
    @23
    @28
    @24
    ax-1cn
    ax-1cn
    c1
    @10
    c1
    subsub23
    mp3an13
    syl
    @22
    @10
    @21
    wceq
    @11
    @21
    @10
    eqcom
    @21
    cc0
    @10
    1m1e0
    eqeq2i
    bitri
    syl6bb
    bitrd
    @0
    @11
    c2
    cc0
    wceq
    #
    @12
    wo
    #
    @12
    @0
    @17
    @25
    @11
    @30
    wb
    2cn
    @27
    c2
    @9
    mul0or
    sylancr
    @29
    wn
    @12
    @30
    wb
    c2
    cc0
    2ne0
    neii
    @29
    @12
    biorf
    ax-mp
    syl6bbr
    @0
    @4
    cc
    wcel
    @12
    @5
    wb
    @26
    @4
    sqeq0
    syl
    3bitrd
    @0
    @19
    @5
    @7
    wb
    @20
    @3
    sineq0
    syl
    @0
    @6
    @8
    cz
    @0
    @17
    @18
    wa
    cpi
    cc
    wcel
    #
    cpi
    cc0
    wne
    #
    wa
    @6
    @8
    wceq
    @17
    @18
    2cn
    2ne0
    pm3.2i
    @31
    @32
    picn
    cpi
    pire
    pipos
    gt0ne0ii
    pm3.2i
    cA
    c2
    cpi
    divdiv1
    mp3an23
    eleq1d
    3bitrd
end
