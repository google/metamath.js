include "com.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "elnn.mm"
include "ancoms.mm"
include "adantll.mm"
include "csuc.mm"
include "wss.mm"
include "word.mm"
include "nnord.mm"
include "ordsucss.mm"
include "syl.mm"
include "ad2antlr.mm"
include "peano2b.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "imbi2d.mm"
include "ssid.mm"
include "2a1i.mm"
include "sssucid.mm"
include "sstr2.mm"
include "mpi.mm"
include "nnasuc.mm"
include "syl5ibr.mm"
include "ex.mm"
include "ad2antrr.mm"
include "a2d.mm"
include "findsg.mm"
include "exp31.mm"
include "syl5bi.mm"
include "com4r.mm"
include "imp31.mm"
include "sseq1d.mm"
include "cvv.mm"
include "ovex.mm"
include "sucssel.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "adantlr.mm"
include "3syld.mm"
include "imp.mm"
include "an32s.mm"
include "mpdan.mm"

theorem nnaordi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( B e. _om /\ C e. _om ) -> ( A e. B -> ( C +o A ) e. ( C +o B ) ) )

  proof
    cC
    com
    wcel
    #
    cB
    com
    wcel
    #
    cA
    cB
    wcel
    #
    cC
    cA
    coa
    co
    #
    cC
    cB
    coa
    co
    #
    wcel
    #
    wi
    @0
    @1
    wa
    #
    @2
    @5
    @6
    @2
    wa
    cA
    com
    wcel
    #
    @5
    @1
    @2
    @7
    @0
    @2
    @1
    @7
    cA
    cB
    elnn
    ancoms
    adantll
    @6
    @7
    @2
    @5
    @6
    @7
    wa
    #
    @2
    @5
    @8
    @2
    cA
    csuc
    #
    cB
    wss
    #
    cC
    @9
    coa
    co
    #
    @4
    wss
    #
    @5
    @1
    @2
    @10
    wi
    #
    @0
    @7
    @1
    cB
    word
    @13
    cB
    nnord
    cA
    cB
    ordsucss
    syl
    ad2antlr
    @0
    @1
    @7
    @10
    @12
    wi
    @1
    @7
    @10
    @0
    @12
    @7
    @9
    com
    wcel
    #
    @1
    @10
    @0
    @12
    wi
    #
    wi
    cA
    peano2b
    @1
    @14
    @10
    @15
    @0
    @11
    cC
    vx
    cv
    #
    coa
    co
    #
    wss
    #
    wi
    @0
    @11
    @11
    wss
    #
    wi
    @0
    @11
    cC
    vy
    cv
    #
    coa
    co
    #
    wss
    #
    wi
    @0
    @11
    cC
    @20
    csuc
    #
    coa
    co
    #
    wss
    #
    wi
    @15
    vx
    vy
    cB
    @9
    @16
    @9
    wceq
    #
    @18
    @19
    @0
    @26
    @17
    @11
    @11
    @16
    @9
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @16
    @20
    wceq
    #
    @18
    @22
    @0
    @27
    @17
    @21
    @11
    @16
    @20
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @16
    @23
    wceq
    #
    @18
    @25
    @0
    @28
    @17
    @24
    @11
    @16
    @23
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @16
    cB
    wceq
    #
    @18
    @12
    @0
    @29
    @17
    @4
    @11
    @16
    cB
    cC
    coa
    oveq2
    sseq2d
    imbi2d
    @19
    @14
    @0
    @11
    ssid
    2a1i
    @20
    com
    wcel
    #
    @14
    wa
    @9
    @20
    wss
    #
    wa
    @0
    @22
    @25
    @30
    @0
    @22
    @25
    wi
    #
    wi
    @14
    @31
    @30
    @0
    @32
    @22
    @25
    @30
    @0
    wa
    #
    @11
    @21
    csuc
    #
    wss
    #
    @22
    @21
    @34
    wss
    @35
    @21
    sssucid
    @11
    @21
    @34
    sstr2
    mpi
    @33
    @24
    @34
    @11
    @0
    @30
    @24
    @34
    wceq
    cC
    @20
    nnasuc
    ancoms
    sseq2d
    syl5ibr
    ex
    ad2antrr
    a2d
    findsg
    exp31
    syl5bi
    com4r
    imp31
    @0
    @7
    @12
    @5
    wi
    @1
    @0
    @7
    wa
    #
    @12
    @3
    csuc
    #
    @4
    wss
    #
    @5
    @36
    @11
    @37
    @4
    cC
    cA
    nnasuc
    sseq1d
    @3
    cvv
    wcel
    @38
    @5
    wi
    cC
    cA
    coa
    ovex
    @3
    @4
    cvv
    sucssel
    ax-mp
    syl6bi
    adantlr
    3syld
    imp
    an32s
    mpdan
    ex
    ancoms
end
