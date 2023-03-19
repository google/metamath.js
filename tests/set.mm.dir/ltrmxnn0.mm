include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "crmx.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wa.mm"
include "cmul.mm"
include "cz.mm"
include "nn0z.mm"
include "frmx.mm"
include "fovcl.mm"
include "sylan2.mm"
include "nn0red.mm"
include "cr.mm"
include "eluzelre.mm"
include "adantr.mm"
include "remulcld.mm"
include "peano2zd.mm"
include "cn.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "crmy.mm"
include "cle.mm"
include "rmxypos.mm"
include "simpld.mm"
include "ltmulgt11.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cexp.mm"
include "cmin.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "nnred.mm"
include "frmy.mm"
include "zred.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "simprd.mm"
include "mulge0d.mm"
include "addge01d.mm"
include "wceq.mm"
include "rmxp1.mm"
include "breqtrrd.mm"
include "ltletrd.mm"
include "nn0uz.mm"
include "oveq2.mm"
include "monotuz.mm"
include "3impb.mm"

theorem ltrmxnn0
  let cA: class A
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M < N <-> ( A rmX M ) < ( A rmX N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    cM
    cN
    clt
    wbr
    cA
    cM
    crmx
    co
    #
    cA
    cN
    crmx
    co
    #
    clt
    wbr
    wb
    @1
    va
    vb
    cM
    cN
    cA
    va
    cv
    #
    crmx
    co
    #
    @2
    @3
    cA
    vb
    cv
    #
    crmx
    co
    #
    cA
    @6
    c1
    caddc
    co
    #
    crmx
    co
    #
    cn0
    cc0
    @1
    @6
    cn0
    wcel
    #
    wa
    #
    @7
    @7
    cA
    cmul
    co
    #
    @9
    @11
    @7
    @10
    @1
    @6
    cz
    wcel
    #
    @7
    cn0
    wcel
    @6
    nn0z
    #
    cA
    @6
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    nn0red
    #
    @11
    @7
    cA
    @15
    @1
    cA
    cr
    wcel
    #
    @10
    c2
    cA
    eluzelre
    adantr
    #
    remulcld
    #
    @11
    @9
    @10
    @1
    @8
    cz
    wcel
    @9
    cn0
    wcel
    @10
    @6
    @14
    peano2zd
    cA
    @8
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    nn0red
    @11
    c1
    cA
    clt
    wbr
    #
    @7
    @12
    clt
    wbr
    #
    @1
    @19
    @10
    @1
    cA
    cn
    wcel
    @19
    cA
    eluz2b2
    simprbi
    adantr
    @11
    @7
    cr
    wcel
    @16
    cc0
    @7
    clt
    wbr
    #
    @19
    @20
    wb
    @15
    @17
    @11
    @21
    cc0
    cA
    @6
    crmy
    co
    #
    cle
    wbr
    #
    cA
    @6
    rmxypos
    #
    simpld
    @7
    cA
    ltmulgt11
    syl3anc
    mpbid
    @11
    @12
    @12
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    @22
    cmul
    co
    #
    caddc
    co
    #
    @9
    cle
    @11
    cc0
    @26
    cle
    wbr
    @12
    @27
    cle
    wbr
    @11
    @25
    @22
    @11
    @25
    @1
    @25
    cn
    wcel
    @10
    @1
    @25
    cn
    csquarenn
    cA
    rmspecnonsq
    eldifad
    adantr
    #
    nnred
    #
    @11
    @22
    @10
    @1
    @13
    @22
    cz
    wcel
    @14
    cA
    @6
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    zred
    #
    @11
    @25
    @11
    @25
    @28
    nnnn0d
    nn0ge0d
    @11
    @21
    @23
    @24
    simprd
    mulge0d
    @11
    @12
    @26
    @18
    @11
    @25
    @22
    @29
    @30
    remulcld
    addge01d
    mpbid
    @10
    @1
    @13
    @9
    @27
    wceq
    @14
    cA
    @6
    rmxp1
    sylan2
    breqtrrd
    ltletrd
    @1
    @4
    cn0
    wcel
    #
    wa
    @5
    @31
    @1
    @4
    cz
    wcel
    @5
    cn0
    wcel
    @4
    nn0z
    cA
    @4
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    nn0red
    nn0uz
    @4
    @8
    cA
    crmx
    oveq2
    @4
    @6
    cA
    crmx
    oveq2
    @4
    cM
    cA
    crmx
    oveq2
    @4
    cN
    cA
    crmx
    oveq2
    monotuz
    3impb
end
