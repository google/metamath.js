include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "crmy.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "wa.mm"
include "cmul.mm"
include "crmx.mm"
include "cz.mm"
include "nn0z.mm"
include "frmy.mm"
include "fovcl.mm"
include "sylan2.mm"
include "zred.mm"
include "cr.mm"
include "eluzelre.mm"
include "adantr.mm"
include "remulcld.mm"
include "frmx.mm"
include "nn0red.mm"
include "readdcld.mm"
include "cle.mm"
include "rmxypos.mm"
include "simprd.mm"
include "eluz2nn.mm"
include "nnge1d.mm"
include "lemulge11d.mm"
include "simpld.mm"
include "ltaddposd.mm"
include "mpbid.mm"
include "lelttrd.mm"
include "wceq.mm"
include "rmyp1.mm"
include "breqtrrd.mm"
include "nn0uz.mm"
include "oveq2.mm"
include "monotuz.mm"
include "3impb.mm"

theorem ltrmynn0
  let cA: class A
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M < N <-> ( A rmY M ) < ( A rmY N ) ) )

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
    crmy
    co
    #
    cA
    cN
    crmy
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
    crmy
    co
    #
    @2
    @3
    cA
    vb
    cv
    #
    crmy
    co
    #
    cA
    @6
    c1
    caddc
    co
    #
    crmy
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
    cA
    @6
    crmx
    co
    #
    caddc
    co
    #
    @9
    clt
    @11
    @7
    @12
    @14
    @11
    @7
    @10
    @1
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    @6
    nn0z
    #
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
    @7
    cA
    @17
    @1
    cA
    cr
    wcel
    @10
    c2
    cA
    eluzelre
    adantr
    #
    remulcld
    #
    @11
    @12
    @13
    @19
    @11
    @13
    @10
    @1
    @15
    @13
    cn0
    wcel
    @16
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
    readdcld
    @11
    @7
    cA
    @17
    @18
    @11
    cc0
    @13
    clt
    wbr
    #
    cc0
    @7
    cle
    wbr
    #
    cA
    @6
    rmxypos
    #
    simprd
    @1
    c1
    cA
    cle
    wbr
    @10
    @1
    cA
    cA
    eluz2nn
    nnge1d
    adantr
    lemulge11d
    @11
    @21
    @12
    @14
    clt
    wbr
    @11
    @21
    @22
    @23
    simpld
    @11
    @13
    @12
    @20
    @19
    ltaddposd
    mpbid
    lelttrd
    @10
    @1
    @15
    @9
    @14
    wceq
    @16
    cA
    @6
    rmyp1
    sylan2
    breqtrrd
    @1
    @4
    cn0
    wcel
    #
    wa
    @5
    @24
    @1
    @4
    cz
    wcel
    @5
    cz
    wcel
    @4
    nn0z
    cA
    @4
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    zred
    nn0uz
    @4
    @8
    cA
    crmy
    oveq2
    @4
    @6
    cA
    crmy
    oveq2
    @4
    cM
    cA
    crmy
    oveq2
    @4
    cN
    cA
    crmy
    oveq2
    monotuz
    3impb
end
