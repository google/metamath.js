include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "cif.mm"
include "cop.mm"
include "csts.mm"
include "cstr.mm"
include "wa.mm"
include "simpr11.mm"
include "simpr12.mm"
include "wi.mm"
include "eluznn.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "ifcld.mm"
include "cr.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "eluzelre.mm"
include "anim12i.mm"
include "adantr.mm"
include "simpl3.mm"
include "3jca.mm"
include "lemaxle.mm"
include "syl.mm"
include "simp1.mm"
include "simp2.mm"
include "pm3.22.mm"
include "3adant1.mm"
include "setsfun0.mm"
include "syl2anc.mm"
include "cun.mm"
include "wceq.mm"
include "3simpa.mm"
include "setsdm.mm"
include "cz.mm"
include "simp3.mm"
include "nnz.mm"
include "ssfzunsn.mm"
include "syl2an23an.mm"
include "eqsstrd.mm"
include "isstruct.mm"
include "3imtr4g.mm"

theorem setsstructOLD
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V


  assert |- ( ( G e. U /\ E e. V /\ I e. ( ZZ>= ` M ) ) -> ( G Struct <. M , N >. -> ( G sSet <. I , E >. ) Struct <. M , if ( I <_ N , N , I ) >. ) )

  proof
    cG
    cU
    wcel
    #
    cE
    cV
    wcel
    #
    cI
    cM
    cuz
    cfv
    #
    wcel
    #
    w3a
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    cG
    c0
    csn
    #
    cdif
    wfun
    #
    cG
    cdm
    #
    cM
    cN
    cfz
    co
    wss
    #
    w3a
    #
    @5
    cI
    cN
    cle
    wbr
    #
    cN
    cI
    cif
    #
    cn
    wcel
    #
    cM
    @15
    cle
    wbr
    #
    w3a
    #
    cG
    cI
    cE
    cop
    csts
    co
    #
    @9
    cdif
    wfun
    #
    @19
    cdm
    #
    cM
    @15
    cfz
    co
    #
    wss
    #
    w3a
    #
    cG
    cM
    cN
    cop
    cstr
    wbr
    @19
    cM
    @15
    cop
    cstr
    wbr
    @4
    @13
    @24
    @4
    @13
    wa
    #
    @18
    @20
    @23
    @25
    @5
    @16
    @17
    @5
    @6
    @7
    @10
    @12
    @4
    simpr11
    @25
    @14
    cN
    cI
    cn
    @5
    @6
    @7
    @10
    @12
    @4
    simpr12
    @4
    @13
    cI
    cn
    wcel
    #
    @3
    @0
    @13
    @26
    wi
    @1
    @13
    @3
    @26
    @8
    @10
    @3
    @26
    wi
    #
    @12
    @5
    @6
    @27
    @7
    @5
    @3
    @26
    cI
    cM
    eluznn
    ex
    3ad2ant1
    3ad2ant1
    com12
    3ad2ant3
    imp
    ifcld
    @25
    cN
    cr
    wcel
    #
    cI
    cr
    wcel
    #
    wa
    #
    cM
    cr
    wcel
    #
    @7
    w3a
    #
    @17
    @4
    @13
    @32
    @3
    @0
    @13
    @32
    wi
    @1
    @13
    @3
    @32
    @8
    @10
    @3
    @32
    wi
    @12
    @8
    @3
    @32
    @8
    @3
    wa
    @30
    @31
    @7
    @8
    @28
    @3
    @29
    @6
    @5
    @28
    @7
    cN
    nnre
    3ad2ant2
    cM
    cI
    eluzelre
    anim12i
    @8
    @31
    @3
    @5
    @6
    @31
    @7
    cM
    nnre
    3ad2ant1
    adantr
    @5
    @6
    @7
    @3
    simpl3
    3jca
    ex
    3ad2ant1
    com12
    3ad2ant3
    imp
    cM
    cN
    cI
    lemaxle
    syl
    3jca
    @25
    @0
    @10
    wa
    @3
    @1
    wa
    #
    @20
    @4
    @0
    @13
    @10
    @0
    @1
    @3
    simp1
    @8
    @10
    @12
    simp2
    anim12i
    @4
    @33
    @13
    @1
    @3
    @33
    @0
    @1
    @3
    pm3.22
    3adant1
    adantr
    @2
    cE
    cG
    cI
    cU
    cV
    setsfun0
    syl2anc
    @25
    @21
    @11
    cI
    csn
    cun
    #
    @22
    @25
    @0
    @1
    wa
    #
    @21
    @34
    wceq
    @4
    @35
    @13
    @0
    @1
    @3
    3simpa
    adantr
    cE
    cG
    cI
    cU
    cV
    setsdm
    syl
    @13
    @12
    cN
    cz
    wcel
    #
    @4
    @3
    @34
    @22
    wss
    @8
    @10
    @12
    simp3
    @8
    @10
    @36
    @12
    @6
    @5
    @36
    @7
    cN
    nnz
    3ad2ant2
    3ad2ant1
    @0
    @1
    @3
    @13
    simpl3
    @11
    cI
    cM
    cN
    ssfzunsn
    syl2an23an
    eqsstrd
    3jca
    ex
    cG
    cM
    cN
    isstruct
    @19
    cM
    @15
    isstruct
    3imtr4g
end
