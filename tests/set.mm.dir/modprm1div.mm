include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cr.mm"
include "clt.mm"
include "prmnn.mm"
include "nnred.mm"
include "prmgt1.mm"
include "1mod.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "cn.mm"
include "wb.mm"
include "simpr.mm"
include "1zzd.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem modprm1div
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ ) -> ( ( A mod P ) = 1 <-> P || ( A - 1 ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    #
    cA
    cP
    cmo
    co
    #
    c1
    wceq
    @3
    c1
    cP
    cmo
    co
    #
    wceq
    #
    cP
    cA
    c1
    cmin
    co
    cdvds
    wbr
    #
    @2
    c1
    @4
    @3
    @0
    c1
    @4
    wceq
    #
    @1
    @0
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @7
    @0
    cP
    cP
    prmnn
    #
    nnred
    cP
    prmgt1
    @8
    @9
    wa
    @4
    c1
    cP
    1mod
    eqcomd
    syl2anc
    adantr
    eqeq2d
    @2
    cP
    cn
    wcel
    #
    @1
    c1
    cz
    wcel
    @5
    @6
    wb
    @0
    @11
    @1
    @10
    adantr
    @0
    @1
    simpr
    @2
    1zzd
    cA
    c1
    cP
    moddvds
    syl3anc
    bitrd
end
