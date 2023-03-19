include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "0csh0.mm"
include "oveq1.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "wne.mm"
include "cop.mm"
include "csubstr.mm"
include "cc0.mm"
include "cconcat.mm"
include "cn.mm"
include "lennncl.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "modabs2.mm"
include "syl2anr.mm"
include "opeq1d.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "ex.mm"
include "syl.mm"
include "impancom.mm"
include "impcom.mm"
include "simprl.mm"
include "simprr.mm"
include "adantr.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "cshword.mm"
include "syl2anc.mm"
include "adantl.mm"
include "3eqtr4rd.mm"
include "pm2.61ine.mm"

theorem cshwmodn
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( W cyclShift N ) = ( W cyclShift ( N mod ( # ` W ) ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    cW
    cN
    cW
    chash
    cfv
    #
    cmo
    co
    #
    ccsh
    co
    #
    wceq
    #
    wi
    cW
    c0
    cW
    c0
    wceq
    #
    @7
    @2
    @8
    c0
    cN
    ccsh
    co
    c0
    @3
    @6
    cN
    0csh0
    cW
    c0
    cN
    ccsh
    oveq1
    @8
    @6
    c0
    @5
    ccsh
    co
    c0
    cW
    c0
    @5
    ccsh
    oveq1
    @5
    0csh0
    syl6eq
    3eqtr4a
    a1d
    cW
    c0
    wne
    #
    @2
    @7
    @9
    @2
    wa
    #
    cW
    @5
    @4
    cmo
    co
    #
    @4
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    @11
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cW
    @5
    @4
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    @5
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    @6
    @3
    @2
    @9
    @16
    @21
    wceq
    #
    @0
    @9
    @1
    @22
    @0
    @9
    wa
    @4
    cn
    wcel
    #
    @1
    @22
    wi
    cV
    cW
    lennncl
    #
    @23
    @1
    @22
    @23
    @1
    wa
    #
    @13
    @18
    @15
    @20
    cconcat
    @25
    @12
    @17
    cW
    csubstr
    @25
    @11
    @5
    @4
    @1
    cN
    cr
    wcel
    @4
    crp
    wcel
    @11
    @5
    wceq
    @23
    cN
    zre
    @4
    nnrp
    cN
    @4
    modabs2
    syl2anr
    #
    opeq1d
    oveq2d
    @25
    @14
    @19
    cW
    csubstr
    @25
    @11
    @5
    cc0
    @26
    opeq2d
    oveq2d
    oveq12d
    ex
    syl
    impancom
    impcom
    @10
    @0
    @5
    cz
    wcel
    @6
    @16
    wceq
    @9
    @0
    @1
    simprl
    @10
    @5
    @10
    cN
    @4
    @9
    @0
    @1
    simprr
    @2
    @9
    @23
    @0
    @9
    @23
    wi
    @1
    @0
    @9
    @23
    @24
    ex
    adantr
    impcom
    zmodcld
    nn0zd
    @5
    cV
    cW
    cshword
    syl2anc
    @2
    @3
    @21
    wceq
    @9
    cN
    cV
    cW
    cshword
    adantl
    3eqtr4rd
    ex
    pm2.61ine
end
