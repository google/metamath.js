include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "1z.mm"
include "gcdaddm.mm"
include "mp3an1.mm"
include "cc.mm"
include "zcn.mm"
include "mulid2.mm"
include "oveq2d.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"

theorem gcdadd
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) = ( M gcd ( N + M ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cM
    cN
    cgcd
    co
    #
    cM
    cN
    c1
    cM
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    cM
    cN
    cM
    caddc
    co
    #
    cgcd
    co
    #
    c1
    cz
    wcel
    @0
    @1
    @2
    @5
    wceq
    1z
    c1
    cM
    cN
    gcdaddm
    mp3an1
    @0
    @5
    @7
    wceq
    #
    @1
    @0
    cM
    cc
    wcel
    #
    @8
    cM
    zcn
    @9
    @4
    @6
    cM
    cgcd
    @9
    @3
    cM
    cN
    caddc
    cM
    mulid2
    oveq2d
    oveq2d
    syl
    adantr
    eqtrd
end
