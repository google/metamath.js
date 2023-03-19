include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cbc.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "wceq.mm"
include "peano2nn0.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "bccmpl.mm"
include "syl2anc.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "pnncand.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "bcn2.mm"
include "cc.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem bcp1m1
  let cN: class N


  assert |- ( N e. NN0 -> ( ( N + 1 ) _C ( N - 1 ) ) = ( ( ( N + 1 ) x. N ) / 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cN
    c1
    cmin
    co
    #
    cbc
    co
    #
    @1
    @1
    @2
    cmin
    co
    #
    cbc
    co
    #
    @1
    cN
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @0
    @1
    cn0
    wcel
    #
    @2
    cz
    wcel
    #
    @3
    @5
    wceq
    cN
    peano2nn0
    #
    @0
    cN
    cz
    wcel
    @9
    cN
    nn0z
    cN
    peano2zm
    syl
    @2
    @1
    bccmpl
    syl2anc
    @0
    @5
    @1
    c2
    cbc
    co
    #
    @7
    @0
    @4
    c2
    @1
    cbc
    @0
    @4
    c1
    c1
    caddc
    co
    c2
    @0
    cN
    c1
    c1
    cN
    nn0cn
    #
    @0
    1cnd
    #
    @13
    pnncand
    df-2
    syl6eqr
    oveq2d
    @0
    @11
    @1
    @1
    c1
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @7
    @0
    @8
    @11
    @16
    wceq
    @10
    @1
    bcn2
    syl
    @0
    @15
    @6
    c2
    cdiv
    @0
    @14
    cN
    @1
    cmul
    @0
    cN
    cc
    wcel
    c1
    cc
    wcel
    @14
    cN
    wceq
    @12
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    oveq1d
    eqtrd
    eqtrd
    eqtrd
end
