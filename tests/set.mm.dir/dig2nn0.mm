include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c2.mm"
include "cdig.mm"
include "cfv.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cmo.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cn.mm"
include "cpnf.mm"
include "cico.mm"
include "wceq.mm"
include "2nn.mm"
include "a1i.mm"
include "simpr.mm"
include "nn0rp0.mm"
include "adantr.mm"
include "digval.mm"
include "syl3anc.mm"
include "cr.mm"
include "2re.mm"
include "wne.mm"
include "2ne0.mm"
include "znegcl.mm"
include "adantl.mm"
include "reexpclzd.mm"
include "nn0re.mm"
include "remulcld.mm"
include "flcld.mm"
include "elmod2.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem dig2nn0
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ K e. ZZ ) -> ( K ( digit ` 2 ) N ) e. { 0 , 1 } )

  proof
    cN
    cn0
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cK
    cN
    c2
    cdig
    cfv
    co
    #
    c2
    cK
    cneg
    #
    cexp
    co
    #
    cN
    cmul
    co
    #
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    cc0
    c1
    cpr
    #
    @2
    c2
    cn
    wcel
    #
    @1
    cN
    cc0
    cpnf
    cico
    co
    wcel
    #
    @3
    @8
    wceq
    @10
    @2
    2nn
    a1i
    @0
    @1
    simpr
    @0
    @11
    @1
    cN
    nn0rp0
    adantr
    c2
    cN
    cK
    digval
    syl3anc
    @2
    @7
    cz
    wcel
    @8
    @9
    wcel
    @2
    @6
    @2
    @5
    cN
    @2
    c2
    @4
    c2
    cr
    wcel
    @2
    2re
    a1i
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    @1
    @4
    cz
    wcel
    @0
    cK
    znegcl
    adantl
    reexpclzd
    @0
    cN
    cr
    wcel
    @1
    cN
    nn0re
    adantr
    remulcld
    flcld
    @7
    elmod2
    syl
    eqeltrd
end
