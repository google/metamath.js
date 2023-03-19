include "cgbe.mm"
include "wcel.mm"
include "cn.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c6.mm"
include "cle.mm"
include "gbepos.mm"
include "gbegt5.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "wb.mm"
include "5nn.mm"
include "nnzi.mm"
include "nnz.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "biimpd.mm"
include "5p1e6.mm"
include "breq1i.mm"
include "syl6ib.mm"
include "sylc.mm"

theorem gbege6
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachEven -> 6 <_ Z )

  proof
    cZ
    cgbe
    wcel
    cZ
    cn
    wcel
    #
    c5
    cZ
    clt
    wbr
    #
    c6
    cZ
    cle
    wbr
    #
    cZ
    gbepos
    cZ
    gbegt5
    @0
    @1
    c5
    c1
    caddc
    co
    #
    cZ
    cle
    wbr
    #
    @2
    @0
    @1
    @4
    @0
    c5
    cz
    wcel
    cZ
    cz
    wcel
    @1
    @4
    wb
    c5
    5nn
    nnzi
    cZ
    nnz
    c5
    cZ
    zltp1le
    sylancr
    biimpd
    @3
    c6
    cZ
    cle
    5p1e6
    breq1i
    syl6ib
    sylc
end
