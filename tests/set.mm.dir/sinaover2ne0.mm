include "cc0.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cioo.mm"
include "wcel.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "elioore.mm"
include "recnd.mm"
include "2cnd.mm"
include "cc.mm"
include "picn.mm"
include "a1i.mm"
include "wne.mm"
include "2ne0.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divdiv1d.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "wn.mm"
include "0zd.mm"
include "cr.mm"
include "2re.mm"
include "remulcli.mm"
include "cxr.mm"
include "0xr.mm"
include "rexrd.mm"
include "id.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "2pos.mm"
include "mulgt0ii.mm"
include "divgt0d.mm"
include "crp.mm"
include "1rp.mm"
include "elrpd.mm"
include "div1d.mm"
include "iooltub.mm"
include "eqbrtrd.mm"
include "ltdiv23d.mm"
include "1e0p1.mm"
include "syl6breq.mm"
include "btwnnz.mm"
include "eqneltrd.mm"
include "wb.mm"
include "halfcld.mm"
include "sineq0.mm"
include "syl.mm"
include "mtbird.mm"
include "neqned.mm"

theorem sinaover2ne0
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. ( 0 (,) ( 2 x. _pi ) ) -> ( sin ` ( A / 2 ) ) =/= 0 )

  proof
    cA
    cc0
    c2
    cpi
    cmul
    co
    #
    cioo
    co
    wcel
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
    @1
    @3
    cc0
    wceq
    #
    @2
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    @1
    @5
    cA
    @0
    cdiv
    co
    #
    cz
    @1
    cA
    c2
    cpi
    @1
    cA
    cA
    cc0
    @0
    elioore
    #
    recnd
    #
    @1
    2cnd
    cpi
    cc
    wcel
    @1
    picn
    a1i
    c2
    cc0
    wne
    @1
    2ne0
    a1i
    cpi
    cc0
    wne
    @1
    cpi
    pire
    pipos
    gt0ne0ii
    a1i
    divdiv1d
    @1
    cc0
    cz
    wcel
    cc0
    @7
    clt
    wbr
    @7
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    @7
    cz
    wcel
    wn
    @1
    0zd
    @1
    cA
    @0
    @8
    @0
    cr
    wcel
    @1
    c2
    cpi
    2re
    pire
    remulcli
    a1i
    #
    @1
    cc0
    cxr
    wcel
    #
    @0
    cxr
    wcel
    #
    @1
    cc0
    cA
    clt
    wbr
    @12
    @1
    0xr
    a1i
    #
    @1
    @0
    @11
    rexrd
    #
    @1
    id
    #
    cc0
    @0
    cA
    ioogtlb
    syl3anc
    cc0
    @0
    clt
    wbr
    @1
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    a1i
    #
    divgt0d
    @1
    @7
    c1
    @10
    clt
    @1
    cA
    c1
    @0
    @8
    c1
    crp
    wcel
    @1
    1rp
    a1i
    @1
    @0
    @11
    @17
    elrpd
    @1
    cA
    c1
    cdiv
    co
    cA
    @0
    clt
    @1
    cA
    @9
    div1d
    @1
    @12
    @13
    @1
    cA
    @0
    clt
    wbr
    @14
    @15
    @16
    cc0
    @0
    cA
    iooltub
    syl3anc
    eqbrtrd
    ltdiv23d
    1e0p1
    syl6breq
    cc0
    @7
    btwnnz
    syl3anc
    eqneltrd
    @1
    @2
    cc
    wcel
    @4
    @6
    wb
    @1
    cA
    @9
    halfcld
    @2
    sineq0
    syl
    mtbird
    neqned
end
