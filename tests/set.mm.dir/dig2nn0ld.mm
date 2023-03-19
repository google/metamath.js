include "cn.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "cuz.mm"
include "wa.mm"
include "c2.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cdig.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "mp1i.mm"
include "simpl.mm"
include "blennn.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "dignnld.mm"
include "syl3anc.mm"

theorem dig2nn0ld
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN /\ K e. ( ZZ>= ` ( #b ` N ) ) ) -> ( K ( digit ` 2 ) N ) = 0 )

  proof
    cN
    cn
    wcel
    #
    cK
    cN
    cblen
    cfv
    #
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    c2
    c2
    cuz
    cfv
    wcel
    #
    @0
    cK
    c2
    cN
    clogb
    co
    cfl
    cfv
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    cK
    cN
    c2
    cdig
    cfv
    co
    cc0
    wceq
    c2
    cz
    wcel
    @5
    @4
    2z
    c2
    uzid
    mp1i
    @0
    @3
    simpl
    @0
    @3
    @8
    @0
    @2
    @7
    cK
    @0
    @1
    @6
    cuz
    cN
    blennn
    fveq2d
    eleq2d
    biimpa
    c2
    cK
    cN
    dignnld
    syl3anc
end
