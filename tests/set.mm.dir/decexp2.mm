include "c4.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "2cn.mm"
include "2nn0.mm"
include "nn0expcli.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "expp1.mm"
include "mp2an.mm"
include "mulcomi.mm"
include "eqtr2i.mm"
include "oveq1i.mm"
include "mulcomli.mm"
include "decbin0.mm"
include "peano2nn0.mm"
include "ax-mp.mm"
include "3eqtr4i.mm"
include "4nn0.mm"
include "nn0mulcli.mm"
include "addid1i.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "df-2.mm"
include "oveq2i.mm"
include "3eqtr2ri.mm"

theorem decexp2
  let cM: class M
  let cN: class N
  assume decexp2.1: |- M e. NN0
  assume decexp2.2: |- ( M + 2 ) = N


  assert |- ( ( 4 x. ( 2 ^ M ) ) + 0 ) = ( 2 ^ N )

  proof
    c4
    c2
    cM
    cexp
    co
    #
    cmul
    co
    #
    c2
    cM
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    @1
    cc0
    caddc
    co
    c2
    cN
    cexp
    co
    c2
    c2
    @0
    cmul
    co
    #
    cmul
    co
    c2
    @2
    cexp
    co
    #
    c2
    cmul
    co
    #
    @1
    @4
    @5
    c2
    @7
    c2
    @0
    2cn
    @0
    c2
    cM
    2nn0
    decexp2.1
    nn0expcli
    #
    nn0cni
    #
    mulcli
    2cn
    @5
    @6
    c2
    cmul
    @6
    @0
    c2
    cmul
    co
    #
    @5
    c2
    cc
    wcel
    #
    cM
    cn0
    wcel
    #
    @6
    @10
    wceq
    2cn
    decexp2.1
    c2
    cM
    expp1
    mp2an
    @0
    c2
    @9
    2cn
    mulcomi
    eqtr2i
    oveq1i
    mulcomli
    @0
    @8
    decbin0
    @11
    @2
    cn0
    wcel
    #
    @4
    @7
    wceq
    2cn
    @12
    @13
    decexp2.1
    cM
    peano2nn0
    ax-mp
    c2
    @2
    expp1
    mp2an
    3eqtr4i
    @1
    @1
    c4
    @0
    4nn0
    @8
    nn0mulcli
    nn0cni
    addid1i
    cN
    @3
    c2
    cexp
    @3
    cM
    c1
    c1
    caddc
    co
    #
    caddc
    co
    cM
    c2
    caddc
    co
    cN
    cM
    c1
    c1
    cM
    decexp2.1
    nn0cni
    ax-1cn
    ax-1cn
    addassi
    c2
    @14
    cM
    caddc
    df-2
    oveq2i
    decexp2.2
    3eqtr2ri
    oveq2i
    3eqtr4i
end
