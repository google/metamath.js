include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "wa.mm"
include "caddc.mm"
include "cfz.mm"
include "3simpa.mm"
include "cn0.mm"
include "wi.mm"
include "lencl.mm"
include "simplr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "nn0addcl.mm"
include "ancoms.mm"
include "adantr.mm"
include "cr.mm"
include "nn0re.mm"
include "anim1i.mm"
include "nn0addge1.mm"
include "syl.mm"
include "breq1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "exp31.mm"
include "syl5com.mm"
include "3imp.mm"
include "eqid.mm"
include "swrdccat3a.mm"
include "sylc.mm"
include "leidd.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "iftrued.mm"
include "swrdid.mm"
include "opeq2.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "3eqtrd.mm"

theorem swrdccatid
  let cA: class A
  let cB: class B
  let cN: class N
  let cV: class V


  assert |- ( ( A e. Word V /\ B e. Word V /\ N = ( # ` A ) ) -> ( ( A ++ B ) substr <. 0 , N >. ) = A )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cN
    cA
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cB
    cconcat
    co
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    cN
    @3
    cle
    wbr
    #
    cA
    @6
    csubstr
    co
    #
    cA
    cB
    cc0
    cN
    @3
    cmin
    co
    cop
    csubstr
    co
    cconcat
    co
    #
    cif
    #
    @9
    cA
    @5
    @1
    @2
    wa
    cN
    cc0
    @3
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    wcel
    #
    @7
    @11
    wceq
    @1
    @2
    @4
    3simpa
    @1
    @2
    @4
    @14
    @1
    @3
    cn0
    wcel
    #
    @2
    @4
    @14
    wi
    #
    cV
    cA
    lencl
    #
    @2
    @12
    cn0
    wcel
    #
    @15
    @16
    wi
    cV
    cB
    lencl
    @18
    @15
    @4
    @14
    @18
    @15
    wa
    #
    @4
    wa
    #
    cN
    cn0
    wcel
    #
    @13
    cn0
    wcel
    #
    cN
    @13
    cle
    wbr
    #
    @14
    @20
    @21
    @15
    @18
    @15
    @4
    simplr
    @4
    @21
    @15
    wb
    @19
    cN
    @3
    cn0
    eleq1
    adantl
    mpbird
    @19
    @22
    @4
    @15
    @18
    @22
    @3
    @12
    nn0addcl
    ancoms
    adantr
    @20
    @23
    @3
    @13
    cle
    wbr
    #
    @19
    @24
    @4
    @19
    @3
    cr
    wcel
    #
    @18
    wa
    #
    @24
    @15
    @18
    @26
    @15
    @25
    @18
    @3
    nn0re
    #
    anim1i
    ancoms
    @3
    @12
    nn0addge1
    syl
    adantr
    @4
    @23
    @24
    wb
    @19
    cN
    @3
    @13
    cle
    breq1
    adantl
    mpbird
    cN
    @13
    elfz2nn0
    syl3anbrc
    exp31
    syl
    syl5com
    3imp
    cA
    cB
    @3
    cN
    cV
    @3
    eqid
    swrdccat3a
    sylc
    @5
    @8
    @9
    @10
    @5
    @8
    @3
    @3
    cle
    wbr
    #
    @1
    @2
    @28
    @4
    @1
    @3
    @1
    @15
    @25
    @17
    @27
    syl
    leidd
    3ad2ant1
    @4
    @1
    @8
    @28
    wb
    @2
    cN
    @3
    @3
    cle
    breq1
    3ad2ant3
    mpbird
    iftrued
    @5
    @9
    cA
    wceq
    #
    cA
    cc0
    @3
    cop
    #
    csubstr
    co
    #
    cA
    wceq
    #
    @1
    @2
    @32
    @4
    cV
    cA
    swrdid
    3ad2ant1
    @4
    @1
    @29
    @32
    wb
    @2
    @4
    @9
    @31
    cA
    @4
    @6
    @30
    cA
    csubstr
    cN
    @3
    cc0
    opeq2
    oveq2d
    eqeq1d
    3ad2ant3
    mpbird
    3eqtrd
end
