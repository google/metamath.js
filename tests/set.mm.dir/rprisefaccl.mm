include "crp.mm"
include "cr.mm"
include "cc.mm"
include "rpssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "1rp.mm"
include "cv.mm"
include "rpmulcl.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "rpre.mm"
include "nn0re.mm"
include "readdcl.mm"
include "syl2an.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "adantr.mm"
include "adantl.mm"
include "rpgt0.mm"
include "nn0ge0.mm"
include "addgtge0.mm"
include "syl22anc.mm"
include "elrpd.mm"
include "risefaccllem.mm"

theorem rprisefaccl
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR+ /\ N e. NN0 ) -> ( A RiseFac N ) e. RR+ )

  proof
    vx
    vy
    cA
    crp
    vk
    cN
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    1rp
    vx
    cv
    vy
    cv
    rpmulcl
    cA
    crp
    wcel
    #
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    cA
    @1
    caddc
    co
    #
    @0
    cA
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @4
    cr
    wcel
    @2
    cA
    rpre
    #
    @1
    nn0re
    #
    cA
    @1
    readdcl
    syl2an
    @3
    @5
    @6
    cc0
    cA
    clt
    wbr
    #
    cc0
    @1
    cle
    wbr
    #
    cc0
    @4
    clt
    wbr
    @0
    @5
    @2
    @7
    adantr
    @2
    @6
    @0
    @8
    adantl
    @0
    @9
    @2
    cA
    rpgt0
    adantr
    @2
    @10
    @0
    @1
    nn0ge0
    adantl
    cA
    @1
    addgtge0
    syl22anc
    elrpd
    risefaccllem
end
