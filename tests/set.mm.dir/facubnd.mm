include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "fveq2.mm"
include "fac0.mm"
include "syl6eq.mm"
include "id.mm"
include "oveq12d.mm"
include "0exp0e1.mm"
include "breq12d.mm"
include "1le1.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cn.mm"
include "faccl.mm"
include "adantr.mm"
include "nnred.mm"
include "cr.mm"
include "nn0re.mm"
include "simpl.mm"
include "reexpcld.mm"
include "nn0p1nn.mm"
include "simpr.mm"
include "nn0ge0.mm"
include "lep1d.mm"
include "leexp1a.mm"
include "syl32anc.mm"
include "letrd.mm"
include "clt.mm"
include "wb.mm"
include "nngt0d.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "facp1.mm"
include "nncnd.mm"
include "expp1d.mm"
include "3brtr4d.mm"
include "ex.mm"
include "nn0ind.mm"

theorem facubnd
  let cN: class N
  let cM: class M
  let vm: setvar m
  let vk: setvar k


  assert |- ( N e. NN0 -> ( ! ` N ) <_ ( N ^ N ) )

  proof
    vm
    cv
    #
    cfa
    cfv
    #
    @0
    @0
    cexp
    co
    #
    cle
    wbr
    c1
    c1
    cle
    wbr
    vk
    cv
    #
    cfa
    cfv
    #
    @3
    @3
    cexp
    co
    #
    cle
    wbr
    #
    @3
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @7
    @7
    cexp
    co
    #
    cle
    wbr
    #
    cN
    cfa
    cfv
    #
    cN
    cN
    cexp
    co
    #
    cle
    wbr
    vm
    vk
    cN
    @0
    cc0
    wceq
    #
    @1
    c1
    @2
    c1
    cle
    @13
    @1
    cc0
    cfa
    cfv
    c1
    @0
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    @13
    @2
    cc0
    cc0
    cexp
    co
    c1
    @13
    @0
    cc0
    @0
    cc0
    cexp
    @13
    id
    #
    @14
    oveq12d
    0exp0e1
    syl6eq
    breq12d
    @0
    @3
    wceq
    #
    @1
    @4
    @2
    @5
    cle
    @0
    @3
    cfa
    fveq2
    @15
    @0
    @3
    @0
    @3
    cexp
    @15
    id
    #
    @16
    oveq12d
    breq12d
    @0
    @7
    wceq
    #
    @1
    @8
    @2
    @9
    cle
    @0
    @7
    cfa
    fveq2
    @17
    @0
    @7
    @0
    @7
    cexp
    @17
    id
    #
    @18
    oveq12d
    breq12d
    @0
    cN
    wceq
    #
    @1
    @11
    @2
    @12
    cle
    @0
    cN
    cfa
    fveq2
    @19
    @0
    cN
    @0
    cN
    cexp
    @19
    id
    #
    @20
    oveq12d
    breq12d
    1le1
    @3
    cn0
    wcel
    #
    @6
    @10
    @21
    @6
    wa
    #
    @4
    @7
    cmul
    co
    #
    @7
    @3
    cexp
    co
    #
    @7
    cmul
    co
    #
    @8
    @9
    cle
    @22
    @4
    @24
    cle
    wbr
    #
    @23
    @25
    cle
    wbr
    #
    @22
    @4
    @5
    @24
    @22
    @4
    @21
    @4
    cn
    wcel
    @6
    @3
    faccl
    adantr
    nnred
    #
    @22
    @3
    @3
    @21
    @3
    cr
    wcel
    #
    @6
    @3
    nn0re
    adantr
    #
    @21
    @6
    simpl
    #
    reexpcld
    @22
    @7
    @3
    @22
    @7
    @21
    @7
    cn
    wcel
    @6
    @3
    nn0p1nn
    adantr
    #
    nnred
    #
    @31
    reexpcld
    #
    @21
    @6
    simpr
    @22
    @29
    @7
    cr
    wcel
    #
    @21
    cc0
    @3
    cle
    wbr
    #
    @3
    @7
    cle
    wbr
    @5
    @24
    cle
    wbr
    @30
    @33
    @31
    @21
    @36
    @6
    @3
    nn0ge0
    adantr
    @22
    @3
    @30
    lep1d
    @3
    @7
    @3
    leexp1a
    syl32anc
    letrd
    @22
    @4
    cr
    wcel
    @24
    cr
    wcel
    @35
    cc0
    @7
    clt
    wbr
    @26
    @27
    wb
    @28
    @34
    @33
    @22
    @7
    @32
    nngt0d
    @4
    @24
    @7
    lemul1
    syl112anc
    mpbid
    @21
    @8
    @23
    wceq
    @6
    @3
    facp1
    adantr
    @22
    @7
    @3
    @22
    @7
    @32
    nncnd
    @31
    expp1d
    3brtr4d
    ex
    nn0ind
end
