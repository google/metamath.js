include "c0v.mm"
include "wne.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "cdiv.mm"
include "csm.mm"
include "wceq.mm"
include "wb.mm"
include "chil.mm"
include "his6.mm"
include "ax-mp.mm"
include "necon3bii.mm"
include "wa.mm"
include "c1.mm"
include "h1de2i.mm"
include "adantl.mm"
include "oveq2d.mm"
include "cmul.mm"
include "cc.mm"
include "hicli.mm"
include "recclzi.mm"
include "ax-hvmulass.mm"
include "mp3an23.mm"
include "syl.mm"
include "ax-1cn.mm"
include "divcan1zi.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "ax-hvmulid.mm"
include "syl6eq.mm"
include "adantr.mm"
include "mulcom.mm"
include "sylancl.mm"
include "divreczi.mm"
include "eqtr4d.mm"
include "ex.mm"
include "divclzi.mm"
include "csh.mm"
include "wss.mm"
include "cch.mm"
include "elexi.mm"
include "snss.mm"
include "mpbi.mm"
include "occl.mm"
include "choccli.mm"
include "chshii.mm"
include "h1did.mm"
include "shmulcl.mm"
include "mp3an13.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "sylbir.mm"

theorem h1de2bi
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume h1de2.1: |- A e. ~H
  assume h1de2.2: |- B e. ~H


  assert |- ( B =/= 0h -> ( A e. ( _|_ ` ( _|_ ` { B } ) ) <-> A = ( ( ( A .ih B ) / ( B .ih B ) ) .h B ) ) )

  proof
    cB
    c0v
    wne
    cB
    cB
    csp
    co
    #
    cc0
    wne
    #
    cA
    cB
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wcel
    #
    cA
    cA
    cB
    csp
    co
    #
    @0
    cdiv
    co
    #
    cB
    csm
    co
    #
    wceq
    #
    wb
    @0
    cc0
    cB
    c0v
    cB
    chil
    wcel
    #
    @0
    cc0
    wceq
    cB
    c0v
    wceq
    wb
    h1de2.2
    cB
    his6
    ax-mp
    necon3bii
    @1
    @5
    @9
    @1
    @5
    @9
    @1
    @5
    wa
    #
    c1
    @0
    cdiv
    co
    #
    @6
    cB
    csm
    co
    #
    csm
    co
    #
    cA
    @8
    @11
    @12
    @0
    cA
    csm
    co
    #
    csm
    co
    #
    @14
    cA
    @11
    @15
    @13
    @12
    csm
    @5
    @15
    @13
    wceq
    @1
    cA
    cB
    h1de2.1
    h1de2.2
    h1de2i
    adantl
    oveq2d
    @1
    @16
    cA
    wceq
    @5
    @1
    @16
    c1
    cA
    csm
    co
    #
    cA
    @1
    @12
    @0
    cmul
    co
    #
    cA
    csm
    co
    #
    @16
    @17
    @1
    @12
    cc
    wcel
    #
    @19
    @16
    wceq
    #
    @0
    cB
    cB
    h1de2.2
    h1de2.2
    hicli
    #
    recclzi
    #
    @20
    @0
    cc
    wcel
    cA
    chil
    wcel
    #
    @21
    @22
    h1de2.1
    @12
    @0
    cA
    ax-hvmulass
    mp3an23
    syl
    @1
    @18
    c1
    cA
    csm
    c1
    @0
    ax-1cn
    @22
    divcan1zi
    oveq1d
    eqtr3d
    @24
    @17
    cA
    wceq
    h1de2.1
    cA
    ax-hvmulid
    ax-mp
    syl6eq
    adantr
    eqtr3d
    @1
    @14
    @8
    wceq
    @5
    @1
    @12
    @6
    cmul
    co
    #
    cB
    csm
    co
    #
    @14
    @8
    @1
    @20
    @26
    @14
    wceq
    #
    @23
    @20
    @6
    cc
    wcel
    #
    @10
    @27
    cA
    cB
    h1de2.1
    h1de2.2
    hicli
    #
    h1de2.2
    @12
    @6
    cB
    ax-hvmulass
    mp3an23
    syl
    @1
    @25
    @7
    cB
    csm
    @1
    @25
    @6
    @12
    cmul
    co
    #
    @7
    @1
    @20
    @28
    @25
    @30
    wceq
    @23
    @29
    @12
    @6
    mulcom
    sylancl
    @6
    @0
    @29
    @22
    divreczi
    eqtr4d
    oveq1d
    eqtr3d
    adantr
    eqtr3d
    ex
    @1
    @5
    @9
    @8
    @4
    wcel
    #
    @1
    @7
    cc
    wcel
    #
    @31
    @6
    @0
    @29
    @22
    divclzi
    @4
    csh
    wcel
    @32
    cB
    @4
    wcel
    #
    @31
    @4
    @3
    @2
    chil
    wss
    #
    @3
    cch
    wcel
    @10
    @34
    h1de2.2
    cB
    chil
    cB
    chil
    h1de2.2
    elexi
    snss
    mpbi
    @2
    occl
    ax-mp
    choccli
    chshii
    @10
    @33
    h1de2.2
    cB
    h1did
    ax-mp
    @7
    cB
    @4
    shmulcl
    mp3an13
    syl
    cA
    @8
    @4
    eleq1
    syl5ibrcom
    impbid
    sylbir
end
