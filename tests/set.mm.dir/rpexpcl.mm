include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "cexp.mm"
include "co.mm"
include "simpl.mm"
include "rpne0.mm"
include "adantr.mm"
include "simpr.mm"
include "cr.mm"
include "cc.mm"
include "rpssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cv.mm"
include "rpmulcl.mm"
include "1rp.mm"
include "c1.mm"
include "cdiv.mm"
include "rpreccl.mm"
include "expcl2lem.mm"
include "syl3anc.mm"

theorem rpexpcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR+ /\ N e. ZZ ) -> ( A ^ N ) e. RR+ )

  proof
    cA
    crp
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    @0
    cA
    cc0
    wne
    #
    @1
    cA
    cN
    cexp
    co
    crp
    wcel
    @0
    @1
    simpl
    @0
    @2
    @1
    cA
    rpne0
    adantr
    @0
    @1
    simpr
    vx
    vy
    cA
    cN
    crp
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    vx
    cv
    #
    vy
    cv
    rpmulcl
    1rp
    @3
    crp
    wcel
    c1
    @3
    cdiv
    co
    crp
    wcel
    @3
    cc0
    wne
    @3
    rpreccl
    adantr
    expcl2lem
    syl3anc
end
