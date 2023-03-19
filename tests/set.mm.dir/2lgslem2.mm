include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "c4.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "csn.mm"
include "cdif.mm"
include "simpl.mm"
include "wceq.mm"
include "elsng.mm"
include "2z.mm"
include "iddvds.mm"
include "ax-mp.mm"
include "breq2.mm"
include "mpbiri.mm"
include "syl6bi.mm"
include "con3dimp.mm"
include "eldifd.mm"
include "oddprm.mm"
include "nnzd.mm"
include "syl.mm"
include "prmz.mm"
include "zred.mm"
include "cr.mm"
include "4re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "adantr.mm"
include "zsubcld.mm"
include "syl5eqel.mm"

theorem 2lgslem2
  let cP: class P
  let cN: class N
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( P e. Prime /\ -. 2 || P ) -> N e. ZZ )

  proof
    cP
    cprime
    wcel
    #
    c2
    cP
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    cN
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    cz
    2lgslem2.n
    @3
    @4
    @6
    @3
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @4
    cz
    wcel
    @3
    cP
    cprime
    @7
    @0
    @2
    simpl
    @0
    cP
    @7
    wcel
    #
    @1
    @0
    @9
    cP
    c2
    wceq
    #
    @1
    cP
    c2
    cprime
    elsng
    @10
    @1
    c2
    c2
    cdvds
    wbr
    #
    c2
    cz
    wcel
    @11
    2z
    c2
    iddvds
    ax-mp
    cP
    c2
    c2
    cdvds
    breq2
    mpbiri
    syl6bi
    con3dimp
    eldifd
    @8
    @4
    cP
    oddprm
    nnzd
    syl
    @0
    @6
    cz
    wcel
    @2
    @0
    @5
    @0
    cP
    c4
    @0
    cP
    cP
    prmz
    zred
    c4
    cr
    wcel
    @0
    4re
    a1i
    c4
    cc0
    wne
    @0
    4ne0
    a1i
    redivcld
    flcld
    adantr
    zsubcld
    syl5eqel
end
