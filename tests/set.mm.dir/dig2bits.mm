include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmo.mm"
include "c1.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cdig.mm"
include "cbits.mm"
include "cz.mm"
include "wb.mm"
include "cr.mm"
include "nn0re.mm"
include "adantr.mm"
include "2re.mm"
include "a1i.mm"
include "reexpcl.mm"
include "sylan.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "nn0z.mm"
include "adantl.mm"
include "expne0d.mm"
include "redivcld.mm"
include "flcld.mm"
include "mod2eq1n2dvds.mm"
include "syl.mm"
include "cn.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "simpr.mm"
include "nn0rp0.mm"
include "nn0digval.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "bitsval2.mm"
include "3bitr4d.mm"

theorem dig2bits
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ K e. NN0 ) -> ( ( K ( digit ` 2 ) N ) = 1 <-> K e. ( bits ` N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cN
    c2
    cK
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    c1
    wceq
    #
    c2
    @5
    cdvds
    wbr
    wn
    #
    cK
    cN
    c2
    cdig
    cfv
    co
    #
    c1
    wceq
    cK
    cN
    cbits
    cfv
    wcel
    #
    @2
    @5
    cz
    wcel
    @7
    @8
    wb
    @2
    @4
    @2
    cN
    @3
    @0
    cN
    cr
    wcel
    @1
    cN
    nn0re
    adantr
    @0
    c2
    cr
    wcel
    #
    @1
    @3
    cr
    wcel
    @11
    @0
    2re
    a1i
    c2
    cK
    reexpcl
    sylan
    @2
    c2
    cK
    @2
    2cnd
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    @1
    cK
    cz
    wcel
    @0
    cK
    nn0z
    adantl
    expne0d
    redivcld
    flcld
    @5
    mod2eq1n2dvds
    syl
    @2
    @9
    @6
    c1
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
    @9
    @6
    wceq
    @12
    @2
    2nn
    a1i
    @0
    @1
    simpr
    @0
    @13
    @1
    cN
    nn0rp0
    adantr
    c2
    cN
    cK
    nn0digval
    syl3anc
    eqeq1d
    @0
    cN
    cz
    wcel
    @1
    @10
    @8
    wb
    cN
    nn0z
    cK
    cN
    bitsval2
    sylan
    3bitr4d
end
