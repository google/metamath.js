include "com.mm"
include "wcel.mm"
include "wss.mm"
include "coa.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "con0.mm"
include "nnon.mm"
include "oa0.mm"
include "adantr.mm"
include "adantl.mm"
include "biimprd.mm"
include "syl2an.mm"
include "word.mm"
include "wb.mm"
include "nnacl.mm"
include "ancoms.mm"
include "adantrr.mm"
include "eloni.mm"
include "3syl.mm"
include "adantrl.mm"
include "ordsucsssuc.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "nnasuc.mm"
include "mpbird.mm"
include "ex.mm"
include "imim2d.mm"
include "a2d.mm"
include "finds.mm"
include "com12.mm"
include "3impia.mm"

theorem nnawordi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( A C_ B -> ( A +o C ) C_ ( B +o C ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cC
    coa
    co
    #
    cB
    cC
    coa
    co
    #
    wss
    #
    wi
    #
    @2
    @0
    @1
    wa
    #
    @7
    @8
    @3
    cA
    vx
    cv
    #
    coa
    co
    #
    cB
    @9
    coa
    co
    #
    wss
    #
    wi
    #
    wi
    @8
    @3
    cA
    c0
    coa
    co
    #
    cB
    c0
    coa
    co
    #
    wss
    #
    wi
    #
    wi
    @8
    @3
    cA
    vy
    cv
    #
    coa
    co
    #
    cB
    @18
    coa
    co
    #
    wss
    #
    wi
    #
    wi
    @8
    @3
    cA
    @18
    csuc
    #
    coa
    co
    #
    cB
    @23
    coa
    co
    #
    wss
    #
    wi
    #
    wi
    @8
    @7
    wi
    vx
    vy
    cC
    @9
    c0
    wceq
    #
    @13
    @17
    @8
    @28
    @12
    @16
    @3
    @28
    @10
    @14
    @11
    @15
    @9
    c0
    cA
    coa
    oveq2
    @9
    c0
    cB
    coa
    oveq2
    sseq12d
    imbi2d
    imbi2d
    vx
    vy
    weq
    #
    @13
    @22
    @8
    @29
    @12
    @21
    @3
    @29
    @10
    @19
    @11
    @20
    @9
    @18
    cA
    coa
    oveq2
    @9
    @18
    cB
    coa
    oveq2
    sseq12d
    imbi2d
    imbi2d
    @9
    @23
    wceq
    #
    @13
    @27
    @8
    @30
    @12
    @26
    @3
    @30
    @10
    @24
    @11
    @25
    @9
    @23
    cA
    coa
    oveq2
    @9
    @23
    cB
    coa
    oveq2
    sseq12d
    imbi2d
    imbi2d
    @9
    cC
    wceq
    #
    @13
    @7
    @8
    @31
    @12
    @6
    @3
    @31
    @10
    @4
    @11
    @5
    @9
    cC
    cA
    coa
    oveq2
    @9
    cC
    cB
    coa
    oveq2
    sseq12d
    imbi2d
    imbi2d
    @0
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    @17
    @1
    cA
    nnon
    cB
    nnon
    @32
    @33
    wa
    #
    @16
    @3
    @34
    @14
    cA
    @15
    cB
    @32
    @14
    cA
    wceq
    @33
    cA
    oa0
    adantr
    @33
    @15
    cB
    wceq
    @32
    cB
    oa0
    adantl
    sseq12d
    biimprd
    syl2an
    @18
    com
    wcel
    #
    @8
    @22
    @27
    @35
    @8
    @22
    @27
    wi
    @35
    @8
    wa
    #
    @21
    @26
    @3
    @36
    @21
    @26
    @36
    @21
    wa
    @26
    @19
    csuc
    #
    @20
    csuc
    #
    wss
    #
    @36
    @21
    @39
    @36
    @19
    word
    #
    @20
    word
    #
    @21
    @39
    wb
    @36
    @19
    com
    wcel
    #
    @19
    con0
    wcel
    @40
    @35
    @0
    @42
    @1
    @0
    @35
    @42
    cA
    @18
    nnacl
    ancoms
    adantrr
    @19
    nnon
    @19
    eloni
    3syl
    @36
    @20
    com
    wcel
    #
    @20
    con0
    wcel
    @41
    @35
    @1
    @43
    @0
    @1
    @35
    @43
    cB
    @18
    nnacl
    ancoms
    adantrl
    @20
    nnon
    @20
    eloni
    3syl
    @19
    @20
    ordsucsssuc
    syl2anc
    biimpa
    @36
    @26
    @39
    wb
    @21
    @36
    @24
    @37
    @25
    @38
    @35
    @0
    @24
    @37
    wceq
    #
    @1
    @0
    @35
    @44
    cA
    @18
    nnasuc
    ancoms
    adantrr
    @35
    @1
    @25
    @38
    wceq
    #
    @0
    @1
    @35
    @45
    cB
    @18
    nnasuc
    ancoms
    adantrl
    sseq12d
    adantr
    mpbird
    ex
    imim2d
    ex
    a2d
    finds
    com12
    3impia
end
