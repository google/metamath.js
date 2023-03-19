include "cn0.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cle.mm"
include "wb.mm"
include "peano2z.mm"
include "degltlem1.mm"
include "sylan2.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "breq2d.mm"
include "adantl.mm"
include "bitrd.mm"

theorem degltp1le
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. ( NN0 u. { -oo } ) /\ Y e. ZZ ) -> ( X < ( Y + 1 ) <-> X <_ Y ) )

  proof
    cX
    cn0
    cmnf
    csn
    cun
    wcel
    #
    cY
    cz
    wcel
    #
    wa
    cX
    cY
    c1
    caddc
    co
    #
    clt
    wbr
    #
    cX
    @2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    cX
    cY
    cle
    wbr
    #
    @1
    @0
    @2
    cz
    wcel
    @3
    @5
    wb
    cY
    peano2z
    cX
    @2
    degltlem1
    sylan2
    @1
    @5
    @6
    wb
    @0
    @1
    @4
    cY
    cX
    cle
    @1
    cY
    cc
    wcel
    c1
    cc
    wcel
    @4
    cY
    wceq
    cY
    zcn
    ax-1cn
    cY
    c1
    pncan
    sylancl
    breq2d
    adantl
    bitrd
end
