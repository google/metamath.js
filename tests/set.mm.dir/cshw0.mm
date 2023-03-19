include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "0csh0.mm"
include "oveq1.mm"
include "id.mm"
include "3eqtr3a.mm"
include "a1d.mm"
include "wne.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "cmo.mm"
include "cz.mm"
include "0z.mm"
include "cshword.mm"
include "mpan2.mm"
include "adantr.mm"
include "necom.mm"
include "cn.mm"
include "crp.mm"
include "lennncl.mm"
include "nnrp.mm"
include "0mod.mm"
include "opeq1d.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "3syl.mm"
include "sylan2b.mm"
include "eqtrd.mm"
include "swrdid.mm"
include "swrd00.mm"
include "a1i.mm"
include "ccatrid.mm"
include "3eqtrd.mm"
include "expcom.mm"
include "pm2.61ine.mm"

theorem cshw0
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( W cyclShift 0 ) = W )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    cc0
    ccsh
    co
    #
    cW
    wceq
    #
    wi
    c0
    cW
    c0
    cW
    wceq
    #
    @2
    @0
    @3
    c0
    cc0
    ccsh
    co
    c0
    @1
    cW
    cc0
    0csh0
    c0
    cW
    cc0
    ccsh
    oveq1
    @3
    id
    3eqtr3a
    a1d
    @0
    c0
    cW
    wne
    #
    @2
    @0
    @4
    wa
    #
    @1
    cW
    cc0
    cW
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    cc0
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cW
    c0
    cconcat
    co
    #
    cW
    @5
    @1
    cW
    cc0
    @6
    cmo
    co
    #
    @6
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    @13
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    @11
    @0
    @1
    @18
    wceq
    #
    @4
    @0
    cc0
    cz
    wcel
    @19
    0z
    cc0
    cV
    cW
    cshword
    mpan2
    adantr
    @4
    @0
    cW
    c0
    wne
    #
    @18
    @11
    wceq
    #
    c0
    cW
    necom
    @0
    @20
    wa
    @6
    cn
    wcel
    @6
    crp
    wcel
    #
    @21
    cV
    cW
    lennncl
    @6
    nnrp
    @22
    @15
    @8
    @17
    @10
    cconcat
    @22
    @14
    @7
    cW
    csubstr
    @22
    @13
    cc0
    @6
    @6
    0mod
    #
    opeq1d
    oveq2d
    @22
    @16
    @9
    cW
    csubstr
    @22
    @13
    cc0
    cc0
    @23
    opeq2d
    oveq2d
    oveq12d
    3syl
    sylan2b
    eqtrd
    @5
    @8
    cW
    @10
    c0
    cconcat
    @0
    @8
    cW
    wceq
    @4
    cV
    cW
    swrdid
    adantr
    @10
    c0
    wceq
    @5
    cW
    cc0
    swrd00
    a1i
    oveq12d
    @0
    @12
    cW
    wceq
    @4
    cV
    cW
    ccatrid
    adantr
    3eqtrd
    expcom
    pm2.61ine
end
