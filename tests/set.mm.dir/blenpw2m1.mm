include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cblen.mm"
include "cfv.mm"
include "clogb.mm"
include "cfl.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "2nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nn0expcld.mm"
include "nnge1.mm"
include "2cnd.mm"
include "exp1d.mm"
include "eqcomd.mm"
include "breq1d.mm"
include "cr.mm"
include "2re.mm"
include "1zzd.mm"
include "nnz.mm"
include "clt.mm"
include "1lt2.mm"
include "leexp2d.mm"
include "bitr4d.mm"
include "mpbird.mm"
include "nn0ge2m1nn.mm"
include "syl2anc.mm"
include "blennn.mm"
include "syl.mm"
include "logbpw2m1.mm"
include "oveq1d.mm"
include "cc.mm"
include "nncn.mm"
include "npcan1.mm"
include "3eqtrd.mm"

theorem blenpw2m1
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( I e. NN -> ( #b ` ( ( 2 ^ I ) - 1 ) ) = I )

  proof
    cI
    cn
    wcel
    #
    c2
    cI
    cexp
    co
    #
    c1
    cmin
    co
    #
    cblen
    cfv
    #
    c2
    @2
    clogb
    co
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cI
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    cI
    @0
    @2
    cn
    wcel
    #
    @3
    @5
    wceq
    @0
    @1
    cn0
    wcel
    c2
    @1
    cle
    wbr
    #
    @8
    @0
    c2
    cI
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    cI
    nnnn0
    nn0expcld
    @0
    @9
    c1
    cI
    cle
    wbr
    #
    cI
    nnge1
    @0
    @9
    c2
    c1
    cexp
    co
    #
    @1
    cle
    wbr
    @10
    @0
    c2
    @11
    @1
    cle
    @0
    @11
    c2
    @0
    c2
    @0
    2cnd
    exp1d
    eqcomd
    breq1d
    @0
    c2
    c1
    cI
    c2
    cr
    wcel
    @0
    2re
    a1i
    @0
    1zzd
    cI
    nnz
    c1
    c2
    clt
    wbr
    @0
    1lt2
    a1i
    leexp2d
    bitr4d
    mpbird
    @1
    nn0ge2m1nn
    syl2anc
    @2
    blennn
    syl
    @0
    @4
    @6
    c1
    caddc
    cI
    logbpw2m1
    oveq1d
    @0
    cI
    cc
    wcel
    @7
    cI
    wceq
    cI
    nncn
    cI
    npcan1
    syl
    3eqtrd
end
