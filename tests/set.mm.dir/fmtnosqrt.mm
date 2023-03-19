include "cn.mm"
include "wcel.mm"
include "cfmtno.mm"
include "cfv.mm"
include "csqrt.mm"
include "cfl.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cn0.mm"
include "wceq.mm"
include "nnnn0.mm"
include "fmtno.mm"
include "syl.mm"
include "fveq2d.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "id.mm"
include "1nn0.mm"
include "a1i.mm"
include "cc0.mm"
include "2nn.mm"
include "2nn0.mm"
include "nnm1nn0.mm"
include "nn0expcld.mm"
include "peano2nn0.mm"
include "nnexpcld.mm"
include "nngt0.mm"
include "cr.mm"
include "wa.mm"
include "wb.mm"
include "nn0red.mm"
include "1re.mm"
include "jca.mm"
include "ltaddpos2.mm"
include "mpbid.mm"
include "3jca.mm"
include "sqrtpwpw2p.mm"
include "eqtrd.mm"

theorem fmtnosqrt
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( |_ ` ( sqrt ` ( FermatNo ` N ) ) ) = ( 2 ^ ( 2 ^ ( N - 1 ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cfmtno
    cfv
    #
    csqrt
    cfv
    #
    cfl
    cfv
    c2
    c2
    cN
    cexp
    co
    cexp
    co
    c1
    caddc
    co
    #
    csqrt
    cfv
    #
    cfl
    cfv
    #
    c2
    c2
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    cexp
    co
    #
    @0
    @2
    @4
    cfl
    @0
    @1
    @3
    csqrt
    @0
    cN
    cn0
    wcel
    @1
    @3
    wceq
    cN
    nnnn0
    cN
    fmtno
    syl
    fveq2d
    fveq2d
    @0
    @0
    c1
    cn0
    wcel
    #
    c1
    c2
    @7
    c1
    caddc
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    clt
    wbr
    #
    w3a
    @5
    @8
    wceq
    @0
    @0
    @9
    @12
    @0
    id
    @9
    @0
    1nn0
    a1i
    @0
    cc0
    @11
    clt
    wbr
    #
    @12
    @0
    @11
    cn
    wcel
    @13
    @0
    c2
    @10
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @0
    @7
    cn0
    wcel
    @10
    cn0
    wcel
    @0
    c2
    @6
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    #
    cN
    nnm1nn0
    nn0expcld
    @7
    peano2nn0
    syl
    #
    nnexpcld
    @11
    nngt0
    syl
    @0
    @11
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    @13
    @12
    wb
    @0
    @16
    @17
    @0
    @11
    @0
    c2
    @10
    @14
    @15
    nn0expcld
    nn0red
    @17
    @0
    1re
    a1i
    jca
    @11
    c1
    ltaddpos2
    syl
    mpbid
    3jca
    c1
    cN
    sqrtpwpw2p
    syl
    eqtrd
end
