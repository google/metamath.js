include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wnel.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cn.mm"
include "wcel.mm"
include "cfz.mm"
include "cif.mm"
include "cmpt.mm"
include "cfv.mm"
include "cprod.mm"
include "id.mm"
include "cmap.mm"
include "wf.mm"
include "eqid.mm"
include "fzfid.mm"
include "eqidd.mm"
include "wceq.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "adantl.mm"
include "elfznn.mm"
include "1nn.mm"
include "a1i.mm"
include "ifcld.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "fprodnncl.mm"
include "fmpti.mm"
include "nnex.mm"
include "elmap.mm"
include "mpbir.mm"
include "cgcd.mm"
include "clt.mm"
include "c2.mm"
include "cprmo.mm"
include "prmgapprmolem.mm"
include "cz.mm"
include "elfzelz.mm"
include "1zzd.mm"
include "prodeq2dv.mm"
include "mpteq2dva.mm"
include "oveq2.mm"
include "prodeq1d.mm"
include "simpl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "prmoval.mm"
include "syl.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "prmgaplem8.mm"
include "rgen.mm"

theorem prmgapprmo
  let vz: setvar z
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m

  disjoint n p
  disjoint n q
  disjoint n z
  disjoint p q
  disjoint p z
  disjoint q z
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint j p
  disjoint j q
  disjoint j z
  disjoint k p
  disjoint k q
  disjoint k z
  disjoint m p
  disjoint m q
  disjoint m z
  assert |- A. n e. NN E. p e. Prime E. q e. Prime ( n <_ ( q - p ) /\ A. z e. ( ( p + 1 ) ..^ q ) z e/ Prime )

  proof
    vn
    cv
    #
    vq
    cv
    #
    vp
    cv
    #
    cmin
    co
    cle
    wbr
    vz
    cv
    cprime
    wnel
    vz
    @2
    c1
    caddc
    co
    @1
    cfzo
    co
    wral
    wa
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    vn
    cn
    @0
    cn
    wcel
    #
    vz
    vi
    vj
    cn
    c1
    vj
    cv
    #
    cfz
    co
    #
    vk
    cv
    #
    vm
    cn
    vm
    cv
    #
    cprime
    wcel
    #
    @7
    c1
    cif
    #
    cmpt
    #
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    @0
    vq
    vp
    @3
    id
    @13
    cn
    cn
    cmap
    co
    wcel
    #
    @3
    @14
    cn
    cn
    @13
    wf
    vj
    cn
    cn
    @12
    @13
    @13
    eqid
    @4
    cn
    wcel
    #
    @5
    @11
    vk
    @15
    c1
    @4
    fzfid
    @15
    @6
    @5
    wcel
    #
    wa
    #
    @11
    @6
    cprime
    wcel
    #
    @6
    c1
    cif
    #
    cn
    @17
    vm
    @6
    @9
    @19
    cn
    @10
    cn
    @17
    @10
    eqidd
    @7
    @6
    wceq
    #
    @9
    @19
    wceq
    #
    @17
    @20
    @8
    @18
    @7
    @6
    c1
    @7
    @6
    cprime
    eleq1
    @20
    id
    ifbieq1d
    #
    adantl
    @16
    @6
    cn
    wcel
    #
    @15
    @6
    @4
    elfznn
    #
    adantl
    @16
    @19
    cn
    wcel
    #
    @15
    @16
    @18
    @6
    c1
    cn
    @24
    c1
    cn
    wcel
    #
    @16
    1nn
    a1i
    ifcld
    adantl
    #
    fvmptd
    @27
    eqeltrd
    fprodnncl
    fmpti
    cn
    cn
    @13
    nnex
    nnex
    elmap
    mpbir
    a1i
    @3
    c1
    @0
    @13
    cfv
    #
    vi
    cv
    #
    caddc
    co
    #
    @29
    cgcd
    co
    #
    clt
    wbr
    vi
    c2
    @0
    cfz
    co
    #
    @3
    @29
    @32
    wcel
    #
    wa
    #
    c1
    @0
    cprmo
    cfv
    #
    @29
    caddc
    co
    #
    @29
    cgcd
    co
    @31
    clt
    @29
    @0
    prmgapprmolem
    @34
    @30
    @36
    @29
    cgcd
    @34
    @28
    @35
    @29
    caddc
    @34
    @28
    c1
    @0
    cfz
    co
    #
    @19
    vk
    cprod
    #
    @35
    @34
    vj
    @0
    @5
    @19
    vk
    cprod
    #
    @38
    cn
    @13
    cn
    @34
    vj
    cn
    @12
    @39
    @34
    @15
    wa
    #
    @5
    @11
    @19
    vk
    @40
    @16
    wa
    #
    vm
    @6
    @9
    @19
    cn
    @10
    cz
    @41
    @10
    eqidd
    @20
    @21
    @41
    @22
    adantl
    @16
    @23
    @40
    @24
    adantl
    @16
    @19
    cz
    wcel
    @40
    @16
    @18
    @6
    c1
    cz
    @6
    c1
    @4
    elfzelz
    @16
    1zzd
    ifcld
    adantl
    fvmptd
    prodeq2dv
    mpteq2dva
    @4
    @0
    wceq
    #
    @39
    @38
    wceq
    @34
    @42
    @5
    @37
    @19
    vk
    @4
    @0
    c1
    cfz
    oveq2
    prodeq1d
    adantl
    @3
    @33
    simpl
    @34
    @37
    @19
    vk
    @34
    c1
    @0
    fzfid
    @6
    @37
    wcel
    #
    @25
    @34
    @43
    @18
    @6
    c1
    cn
    @6
    @0
    elfznn
    @26
    @43
    1nn
    a1i
    ifcld
    adantl
    fprodnncl
    fvmptd
    @3
    @38
    @35
    wceq
    @33
    @3
    @35
    @38
    @3
    @0
    cn0
    wcel
    @35
    @38
    wceq
    @0
    nnnn0
    vk
    @0
    prmoval
    syl
    eqcomd
    adantr
    eqtrd
    oveq1d
    oveq1d
    breqtrrd
    ralrimiva
    prmgaplem8
    rgen
end
