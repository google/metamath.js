include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "crmy.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "id.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "0le0.mm"
include "rmy0.mm"
include "syl5breqr.mm"
include "w3a.mm"
include "cz.mm"
include "nn0z.mm"
include "3ad2ant1.mm"
include "peano2zd.mm"
include "zred.mm"
include "simp2.mm"
include "frmy.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "cr.mm"
include "nn0re.mm"
include "1red.mm"
include "simp3.mm"
include "leadd1dd.mm"
include "clt.mm"
include "ltp1d.mm"
include "wb.mm"
include "ltrmy.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "zltp1le.mm"
include "letrd.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem rmygeid
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> N <_ ( A rmY N ) )

  proof
    cN
    cn0
    wcel
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cA
    cN
    crmy
    co
    #
    cle
    wbr
    #
    @1
    va
    cv
    #
    cA
    @4
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    cc0
    cA
    cc0
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    vb
    cv
    #
    cA
    @9
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    @9
    c1
    caddc
    co
    #
    cA
    @12
    crmy
    co
    #
    cle
    wbr
    #
    wi
    @1
    @3
    wi
    va
    vb
    cN
    @4
    cc0
    wceq
    #
    @6
    @8
    @1
    @15
    @4
    cc0
    @5
    @7
    cle
    @15
    id
    @4
    cc0
    cA
    crmy
    oveq2
    breq12d
    imbi2d
    va
    vb
    weq
    #
    @6
    @11
    @1
    @16
    @4
    @9
    @5
    @10
    cle
    @16
    id
    @4
    @9
    cA
    crmy
    oveq2
    breq12d
    imbi2d
    @4
    @12
    wceq
    #
    @6
    @14
    @1
    @17
    @4
    @12
    @5
    @13
    cle
    @17
    id
    @4
    @12
    cA
    crmy
    oveq2
    breq12d
    imbi2d
    @4
    cN
    wceq
    #
    @6
    @3
    @1
    @18
    @4
    cN
    @5
    @2
    cle
    @18
    id
    @4
    cN
    cA
    crmy
    oveq2
    breq12d
    imbi2d
    @1
    cc0
    cc0
    @7
    cle
    0le0
    cA
    rmy0
    syl5breqr
    @9
    cn0
    wcel
    #
    @1
    @11
    @14
    @19
    @1
    @11
    @14
    @19
    @1
    @11
    w3a
    #
    @12
    @10
    c1
    caddc
    co
    #
    @13
    @20
    @12
    @20
    @9
    @19
    @1
    @9
    cz
    wcel
    #
    @11
    @9
    nn0z
    3ad2ant1
    #
    peano2zd
    #
    zred
    @20
    @21
    @20
    @10
    @20
    @1
    @22
    @10
    cz
    wcel
    #
    @19
    @1
    @11
    simp2
    #
    @23
    cA
    @9
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    #
    peano2zd
    zred
    @20
    @13
    @20
    @1
    @12
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    @26
    @24
    cA
    @12
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    #
    zred
    @20
    @9
    @10
    c1
    @19
    @1
    @9
    cr
    wcel
    @11
    @9
    nn0re
    3ad2ant1
    #
    @20
    @10
    @27
    zred
    @20
    1red
    @19
    @1
    @11
    simp3
    leadd1dd
    @20
    @10
    @13
    clt
    wbr
    #
    @21
    @13
    cle
    wbr
    #
    @20
    @9
    @12
    clt
    wbr
    #
    @32
    @20
    @9
    @31
    ltp1d
    @20
    @1
    @22
    @28
    @34
    @32
    wb
    @26
    @23
    @24
    cA
    @9
    @12
    ltrmy
    syl3anc
    mpbid
    @20
    @25
    @29
    @32
    @33
    wb
    @27
    @30
    @10
    @13
    zltp1le
    syl2anc
    mpbid
    letrd
    3exp
    a2d
    nn0ind
    impcom
end
