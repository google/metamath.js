include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wne.mm"
include "c0h.mm"
include "wceq.mm"
include "wi.mm"
include "wo.mm"
include "wa.mm"
include "wcel.mm"
include "cv.mm"
include "c0v.mm"
include "wrex.mm"
include "chne0i.mm"
include "ssel.mm"
include "csm.mm"
include "co.mm"
include "cc.mm"
include "h1de2ci.mm"
include "cc0.mm"
include "oveq1.mm"
include "chil.mm"
include "ax-hvmul0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqeq1.mm"
include "syl5ibr.mm"
include "necon3d.mm"
include "adantl.mm"
include "c1.mm"
include "cdiv.mm"
include "reccl.mm"
include "csh.mm"
include "chshii.mm"
include "shmulcl.mm"
include "mp3an1.mm"
include "ex.mm"
include "syl.mm"
include "adantr.mm"
include "oveq2.mm"
include "cmul.mm"
include "simpl.mm"
include "ax-hvmulass.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "recid2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "ax-hvmulid.mm"
include "sylan9eqr.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "exp31.mm"
include "com23.mm"
include "imp.mm"
include "syld.mm"
include "com3r.mm"
include "expd.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "sylcom.mm"
include "snssi.mm"
include "chssii.mm"
include "occon2i.mm"
include "ococi.mm"
include "syl6sseq.mm"
include "syl6.mm"
include "anc2li.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "necon1d.mm"
include "neor.mm"
include "sylibr.mm"

theorem h1datomi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume h1datom.1: |- A e. CH
  assume h1datom.2: |- B e. ~H


  assert |- ( A C_ ( _|_ ` ( _|_ ` { B } ) ) -> ( A = ( _|_ ` ( _|_ ` { B } ) ) \/ A = 0H ) )

  proof
    cA
    cB
    csn
    #
    cort
    cfv
    cort
    cfv
    #
    wss
    #
    cA
    @1
    wne
    cA
    c0h
    wceq
    #
    wi
    cA
    @1
    wceq
    #
    @3
    wo
    @2
    cA
    c0h
    cA
    @1
    @2
    cA
    c0h
    wne
    #
    @2
    @1
    cA
    wss
    #
    wa
    @4
    @2
    @5
    @6
    @2
    @5
    cB
    cA
    wcel
    #
    @6
    @5
    vx
    cv
    #
    c0v
    wne
    #
    vx
    cA
    wrex
    @2
    @7
    vx
    cA
    h1datom.1
    chne0i
    @2
    @9
    @7
    vx
    cA
    @2
    @8
    cA
    wcel
    #
    @8
    @1
    wcel
    #
    @9
    @7
    wi
    #
    cA
    @1
    @8
    ssel
    @11
    @8
    vy
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vy
    cc
    wrex
    @10
    @12
    vy
    @8
    cB
    h1datom.2
    h1de2ci
    @10
    @15
    @12
    vy
    cc
    @10
    @13
    cc
    wcel
    #
    @15
    @12
    @16
    @15
    wa
    #
    @9
    @10
    @7
    @17
    @9
    @13
    cc0
    wne
    #
    @10
    @7
    wi
    #
    @15
    @9
    @18
    wi
    @16
    @15
    @13
    cc0
    @8
    c0v
    @13
    cc0
    wceq
    #
    @8
    c0v
    wceq
    @15
    @14
    c0v
    wceq
    @20
    @14
    cc0
    cB
    csm
    co
    #
    c0v
    @13
    cc0
    cB
    csm
    oveq1
    cB
    chil
    wcel
    #
    @21
    c0v
    wceq
    h1datom.2
    cB
    ax-hvmul0
    ax-mp
    syl6eq
    @8
    @14
    c0v
    eqeq1
    syl5ibr
    necon3d
    adantl
    @16
    @15
    @18
    @19
    wi
    @16
    @18
    @15
    @19
    @16
    @18
    @15
    @19
    @16
    @18
    wa
    #
    @15
    wa
    #
    @10
    c1
    @13
    cdiv
    co
    #
    @8
    csm
    co
    #
    cA
    wcel
    #
    @7
    @23
    @10
    @27
    wi
    #
    @15
    @23
    @25
    cc
    wcel
    #
    @28
    @13
    reccl
    #
    @29
    @10
    @27
    cA
    csh
    wcel
    @29
    @10
    @27
    cA
    h1datom.1
    chshii
    @25
    @8
    cA
    shmulcl
    mp3an1
    ex
    syl
    adantr
    @24
    @26
    cB
    cA
    @15
    @23
    @26
    @25
    @14
    csm
    co
    #
    cB
    @8
    @14
    @25
    csm
    oveq2
    @23
    @31
    c1
    cB
    csm
    co
    #
    cB
    @23
    @25
    @13
    cmul
    co
    #
    cB
    csm
    co
    #
    @31
    @32
    @23
    @29
    @16
    @34
    @31
    wceq
    #
    @30
    @16
    @18
    simpl
    @29
    @16
    @22
    @35
    h1datom.2
    @25
    @13
    cB
    ax-hvmulass
    mp3an3
    syl2anc
    @23
    @33
    c1
    cB
    csm
    @13
    recid2
    oveq1d
    eqtr3d
    @22
    @32
    cB
    wceq
    h1datom.2
    cB
    ax-hvmulid
    ax-mp
    syl6eq
    sylan9eqr
    eleq1d
    sylibd
    exp31
    com23
    imp
    syld
    com3r
    expd
    rexlimdv
    syl5bi
    sylcom
    rexlimdv
    syl5bi
    @7
    @1
    cA
    cort
    cfv
    cort
    cfv
    #
    cA
    @7
    @0
    cA
    wss
    @1
    @36
    wss
    cB
    cA
    snssi
    @0
    cA
    @22
    @0
    chil
    wss
    h1datom.2
    cB
    chil
    snssi
    ax-mp
    cA
    h1datom.1
    chssii
    occon2i
    syl
    cA
    h1datom.1
    ococi
    syl6sseq
    syl6
    anc2li
    cA
    @1
    eqss
    syl6ibr
    necon1d
    @3
    cA
    @1
    neor
    sylibr
end
