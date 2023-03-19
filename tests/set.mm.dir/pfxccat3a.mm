include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cconcat.mm"
include "cpfx.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "wceq.mm"
include "w3a.mm"
include "simprl.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "chash.mm"
include "cfv.mm"
include "lencl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "simpl.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "pfxccatpfx1.mm"
include "syl.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c1.mm"
include "wi.mm"
include "eleq1i.mm"
include "wb.mm"
include "clt.mm"
include "nn0ltp1le.mm"
include "cr.mm"
include "nn0re.mm"
include "ltnle.mm"
include "syl2an.mm"
include "bitr3d.mm"
include "3ad2antr1.mm"
include "simpr3.mm"
include "anim1i.mm"
include "ancomd.mm"
include "cz.mm"
include "nn0z.mm"
include "3ad2ant1.mm"
include "peano2nn0.mm"
include "nn0zd.mm"
include "3ad2ant2.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbird.mm"
include "sylbir.mm"
include "syl5bi.mm"
include "imp.mm"
include "impcom.mm"
include "pfxccatpfx2.mm"
include "iffalse.mm"
include "pm2.61ian.mm"

theorem pfxccat3a
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume pfxccatin12.l: |- L = ( # ` A )
  assume pfxccatpfx2.m: |- M = ( # ` B )


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( N e. ( 0 ... ( L + M ) ) -> ( ( A ++ B ) prefix N ) = if ( N <_ L , ( A prefix N ) , ( A ++ ( B prefix ( N - L ) ) ) ) ) )

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
    wa
    #
    cN
    cc0
    cL
    cM
    caddc
    co
    #
    cfz
    co
    wcel
    #
    cA
    cB
    cconcat
    co
    cN
    cpfx
    co
    #
    cN
    cL
    cle
    wbr
    #
    cA
    cN
    cpfx
    co
    #
    cA
    cB
    cN
    cL
    cmin
    co
    cpfx
    co
    cconcat
    co
    #
    cif
    #
    wceq
    #
    @7
    @3
    @5
    wa
    #
    @11
    @7
    @12
    wa
    #
    @6
    @8
    @10
    @13
    @1
    @2
    cN
    cc0
    cL
    cfz
    co
    wcel
    #
    w3a
    #
    @6
    @8
    wceq
    @13
    @3
    @14
    @15
    @7
    @3
    @5
    simprl
    @13
    cN
    cn0
    wcel
    #
    cL
    cn0
    wcel
    #
    @7
    @14
    @12
    @16
    @7
    @5
    @16
    @3
    cN
    @4
    elfznn0
    adantl
    adantl
    @12
    @17
    @7
    @3
    @17
    @5
    @1
    @17
    @2
    @1
    cL
    cA
    chash
    cfv
    #
    cn0
    pfxccatin12.l
    cV
    cA
    lencl
    #
    syl5eqel
    adantr
    adantr
    adantl
    @7
    @12
    simpl
    cN
    cL
    elfz2nn0
    syl3anbrc
    @1
    @2
    @14
    df-3an
    sylanbrc
    cA
    cB
    cL
    cN
    cV
    pfxccatin12.l
    pfxccatpfx1
    syl
    @7
    @10
    @8
    wceq
    @12
    @7
    @8
    @9
    iftrue
    adantr
    eqtr4d
    @7
    wn
    #
    @12
    wa
    #
    @6
    @9
    @10
    @21
    @1
    @2
    cN
    cL
    c1
    caddc
    co
    #
    @4
    cfz
    co
    wcel
    #
    w3a
    #
    @6
    @9
    wceq
    @21
    @3
    @23
    @24
    @20
    @3
    @5
    simprl
    @12
    @20
    @23
    @3
    @5
    @20
    @23
    wi
    #
    @5
    @16
    @4
    cn0
    wcel
    #
    cN
    @4
    cle
    wbr
    #
    w3a
    #
    @3
    @25
    cN
    @4
    elfz2nn0
    @1
    @28
    @25
    wi
    #
    @2
    @1
    @18
    cn0
    wcel
    #
    @29
    @19
    @30
    @17
    @29
    cL
    @18
    cn0
    pfxccatin12.l
    eleq1i
    @17
    @28
    @25
    @17
    @28
    wa
    #
    @20
    @22
    cN
    cle
    wbr
    #
    @23
    @17
    @26
    @16
    @32
    @20
    wb
    @27
    @17
    @16
    wa
    cL
    cN
    clt
    wbr
    #
    @32
    @20
    cL
    cN
    nn0ltp1le
    @17
    cL
    cr
    wcel
    cN
    cr
    wcel
    @33
    @20
    wb
    @16
    cL
    nn0re
    cN
    nn0re
    cL
    cN
    ltnle
    syl2an
    bitr3d
    3ad2antr1
    @31
    @32
    @23
    @31
    @32
    wa
    #
    @23
    @32
    @27
    wa
    #
    @34
    @27
    @32
    @31
    @27
    @32
    @17
    @16
    @26
    @27
    simpr3
    anim1i
    ancomd
    @34
    cN
    cz
    wcel
    #
    @22
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @23
    @35
    wb
    @31
    @36
    @32
    @28
    @36
    @17
    @16
    @26
    @36
    @27
    cN
    nn0z
    3ad2ant1
    adantl
    adantr
    @31
    @37
    @32
    @17
    @37
    @28
    @17
    @22
    cL
    peano2nn0
    nn0zd
    adantr
    adantr
    @31
    @38
    @32
    @28
    @38
    @17
    @26
    @16
    @38
    @27
    @4
    nn0z
    3ad2ant2
    adantl
    adantr
    cN
    @22
    @4
    elfz
    syl3anc
    mpbird
    ex
    sylbird
    ex
    sylbir
    syl
    adantr
    syl5bi
    imp
    impcom
    @1
    @2
    @23
    df-3an
    sylanbrc
    cA
    cB
    cL
    cM
    cN
    cV
    pfxccatin12.l
    pfxccatpfx2.m
    pfxccatpfx2
    syl
    @20
    @10
    @9
    wceq
    @12
    @7
    @8
    @9
    iffalse
    adantr
    eqtr4d
    pm2.61ian
    ex
end
