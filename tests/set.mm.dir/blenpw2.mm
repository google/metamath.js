include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cblen.mm"
include "cfv.mm"
include "clogb.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cn.mm"
include "wceq.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "blennn.mm"
include "syl.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "mp1i.mm"
include "nn0z.mm"
include "nnlogbexp.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "flid.mm"
include "eqtrd.mm"
include "oveq1d.mm"

theorem blenpw2
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( I e. NN0 -> ( #b ` ( 2 ^ I ) ) = ( I + 1 ) )

  proof
    cI
    cn0
    wcel
    #
    c2
    cI
    cexp
    co
    #
    cblen
    cfv
    #
    c2
    @1
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cI
    c1
    caddc
    co
    @0
    @1
    cn
    wcel
    #
    @2
    @5
    wceq
    c2
    cn
    wcel
    @0
    @6
    2nn
    c2
    cI
    nnexpcl
    mpan
    @1
    blennn
    syl
    @0
    @4
    cI
    c1
    caddc
    @0
    @4
    cI
    cfl
    cfv
    #
    cI
    @0
    @3
    cI
    cfl
    @0
    c2
    c2
    cuz
    cfv
    wcel
    #
    cI
    cz
    wcel
    #
    @3
    cI
    wceq
    c2
    cz
    wcel
    @8
    @0
    2z
    c2
    uzid
    mp1i
    cI
    nn0z
    #
    c2
    cI
    nnlogbexp
    syl2anc
    fveq2d
    @0
    @9
    @7
    cI
    wceq
    @10
    cI
    flid
    syl
    eqtrd
    oveq1d
    eqtrd
end
