include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "cphi.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cn.mm"
include "wceq.mm"
include "1nn.mm"
include "phiprmpw.mm"
include "mpan2.mm"
include "prmz.mm"
include "zcnd.mm"
include "exp1d.mm"
include "fveq2d.mm"
include "cc0.mm"
include "1m1e0.mm"
include "oveq2i.mm"
include "exp0d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem phiprm
  let cP: class P


  assert |- ( P e. Prime -> ( phi ` P ) = ( P - 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    c1
    cexp
    co
    #
    cphi
    cfv
    #
    cP
    c1
    c1
    cmin
    co
    #
    cexp
    co
    #
    cP
    c1
    cmin
    co
    #
    cmul
    co
    #
    cP
    cphi
    cfv
    @5
    @0
    c1
    cn
    wcel
    @2
    @6
    wceq
    1nn
    cP
    c1
    phiprmpw
    mpan2
    @0
    @1
    cP
    cphi
    @0
    cP
    @0
    cP
    cP
    prmz
    zcnd
    #
    exp1d
    fveq2d
    @0
    @6
    c1
    @5
    cmul
    co
    @5
    @0
    @4
    c1
    @5
    cmul
    @0
    @4
    cP
    cc0
    cexp
    co
    c1
    @3
    cc0
    cP
    cexp
    1m1e0
    oveq2i
    @0
    cP
    @7
    exp0d
    syl5eq
    oveq1d
    @0
    @5
    @0
    cP
    cc
    wcel
    c1
    cc
    wcel
    @5
    cc
    wcel
    @7
    ax-1cn
    cP
    c1
    subcl
    sylancl
    mulid2d
    eqtrd
    3eqtr3d
end
