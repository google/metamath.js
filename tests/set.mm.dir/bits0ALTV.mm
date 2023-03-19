include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cbits.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "codd.mm"
include "cn0.mm"
include "wb.mm"
include "0nn0.mm"
include "bitsval2.mm"
include "mpan2.mm"
include "c1.mm"
include "cc.mm"
include "wceq.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "zcn.mm"
include "div1d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "flid.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "notbid.mm"
include "isodd3.mm"
include "baibr.mm"
include "3bitrd.mm"

theorem bits0ALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ZZ -> ( 0 e. ( bits ` N ) <-> N e. Odd ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    cN
    cbits
    cfv
    wcel
    #
    c2
    cN
    c2
    cc0
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    #
    cN
    codd
    wcel
    #
    @0
    cc0
    cn0
    wcel
    @1
    @6
    wb
    0nn0
    cc0
    cN
    bitsval2
    mpan2
    @0
    @5
    @7
    @0
    @4
    cN
    c2
    cdvds
    @0
    @4
    cN
    cfl
    cfv
    cN
    @0
    @3
    cN
    cfl
    @0
    @3
    cN
    c1
    cdiv
    co
    cN
    @2
    c1
    cN
    cdiv
    c2
    cc
    wcel
    @2
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    oveq2i
    @0
    cN
    cN
    zcn
    div1d
    syl5eq
    fveq2d
    cN
    flid
    eqtrd
    breq2d
    notbid
    @9
    @0
    @8
    cN
    isodd3
    baibr
    3bitrd
end
