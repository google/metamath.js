include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "ccxp.mm"
include "cexp.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "cr.mm"
include "2re.mm"
include "nndivre.mm"
include "mpan.mm"
include "recnd.mm"
include "nnnn0.mm"
include "cxpmul2d.mm"
include "2cnd.mm"
include "nncn.mm"
include "nnne0.mm"
include "divcan1d.mm"
include "oveq2d.mm"
include "cn0.mm"
include "wceq.mm"
include "2nn0.mm"
include "cxpexp.mm"
include "mp2an.mm"
include "ax-1cn.mm"
include "sqneg.mm"
include "ax-mp.mm"
include "sq1.mm"
include "3eqtri.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem root1id
  let cN: class N


  assert |- ( N e. NN -> ( ( -u 1 ^c ( 2 / N ) ) ^ N ) = 1 )

  proof
    cN
    cn
    wcel
    #
    c1
    cneg
    #
    c2
    cN
    cdiv
    co
    #
    cN
    cmul
    co
    #
    ccxp
    co
    #
    @1
    @2
    ccxp
    co
    cN
    cexp
    co
    c1
    @0
    @1
    @2
    cN
    @1
    cc
    wcel
    #
    @0
    neg1cn
    a1i
    @0
    @2
    c2
    cr
    wcel
    @0
    @2
    cr
    wcel
    2re
    c2
    cN
    nndivre
    mpan
    recnd
    cN
    nnnn0
    cxpmul2d
    @0
    @4
    @1
    c2
    ccxp
    co
    #
    c1
    @0
    @3
    c2
    @1
    ccxp
    @0
    c2
    cN
    @0
    2cnd
    cN
    nncn
    cN
    nnne0
    divcan1d
    oveq2d
    @6
    @1
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    c1
    @5
    c2
    cn0
    wcel
    @6
    @7
    wceq
    neg1cn
    2nn0
    @1
    c2
    cxpexp
    mp2an
    c1
    cc
    wcel
    @7
    @8
    wceq
    ax-1cn
    c1
    sqneg
    ax-mp
    sq1
    3eqtri
    syl6eq
    eqtr3d
end
