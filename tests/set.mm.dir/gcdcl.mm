include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cgcd.mm"
include "co.mm"
include "cn0.mm"
include "oveq12.mm"
include "gcd0val.mm"
include "syl6eq.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "wn.mm"
include "gcdn0cl.mm"
include "nnnn0d.mm"
include "pm2.61dan.mm"

theorem gcdcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) e. NN0 )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cn0
    wcel
    #
    @1
    @3
    @0
    @1
    @2
    cc0
    cn0
    @1
    @2
    cc0
    cc0
    cgcd
    co
    cc0
    cM
    cc0
    cN
    cc0
    cgcd
    oveq12
    gcd0val
    syl6eq
    0nn0
    syl6eqel
    adantl
    @0
    @1
    wn
    wa
    @2
    cM
    cN
    gcdn0cl
    nnnn0d
    pm2.61dan
end
