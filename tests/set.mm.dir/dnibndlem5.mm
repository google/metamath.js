include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "wa.mm"
include "id.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "readdcl.mm"
include "syl.mm"
include "flltp1.mm"
include "wceq.mm"
include "cc.mm"
include "ax-1cn.mm"
include "2halves.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "w3a.mm"
include "reflcl.mm"
include "recnd.mm"
include "3jca.mm"
include "addass.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "ltadd1d.mm"
include "mpbird.mm"
include "posdifd.mm"
include "mpbid.mm"

theorem dnibndlem5
  let cA: class A


  assert |- ( A e. RR -> 0 < ( ( ( |_ ` ( A + ( 1 / 2 ) ) ) + ( 1 / 2 ) ) - A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cA
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @1
    caddc
    co
    #
    clt
    wbr
    #
    cc0
    @4
    cA
    cmin
    co
    clt
    wbr
    @0
    @5
    @2
    @4
    @1
    caddc
    co
    #
    clt
    wbr
    @0
    @2
    @3
    c1
    caddc
    co
    #
    @6
    clt
    @0
    @2
    cr
    wcel
    #
    @2
    @7
    clt
    wbr
    @0
    @0
    @1
    cr
    wcel
    #
    wa
    @8
    @0
    @0
    @9
    @0
    id
    #
    @9
    @0
    halfre
    a1i
    #
    jca
    cA
    @1
    readdcl
    syl
    #
    @2
    flltp1
    syl
    @0
    @7
    @3
    @1
    @1
    caddc
    co
    #
    caddc
    co
    #
    @6
    @0
    c1
    @13
    @3
    caddc
    c1
    @13
    wceq
    @0
    @13
    c1
    c1
    cc
    wcel
    @13
    c1
    wceq
    ax-1cn
    c1
    2halves
    ax-mp
    eqcomi
    a1i
    oveq2d
    @0
    @6
    @14
    @0
    @3
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @16
    w3a
    @6
    @14
    wceq
    @0
    @15
    @16
    @16
    @0
    @3
    @0
    @8
    @3
    cr
    wcel
    #
    @12
    @2
    reflcl
    syl
    #
    recnd
    @0
    @1
    @11
    recnd
    #
    @19
    3jca
    @3
    @1
    @1
    addass
    syl
    eqcomd
    eqtrd
    breqtrd
    @0
    cA
    @4
    @1
    @10
    @0
    @17
    @9
    wa
    @4
    cr
    wcel
    @0
    @17
    @9
    @18
    @11
    jca
    @3
    @1
    readdcl
    syl
    #
    @11
    ltadd1d
    mpbird
    @0
    cA
    @4
    @10
    @20
    posdifd
    mpbid
end
