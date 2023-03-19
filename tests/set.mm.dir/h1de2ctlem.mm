include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "wi.mm"
include "c0v.mm"
include "cc0.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "chil.mm"
include "elexi.mm"
include "elsn.mm"
include "hsn0elch.mm"
include "ococi.mm"
include "eleq2i.mm"
include "ax-hvmul0.mm"
include "ax-mp.mm"
include "eqeq2i.mm"
include "3bitr4ri.mm"
include "syl6rbbr.mm"
include "0cn.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan.mm"
include "syl6bir.mm"
include "wne.mm"
include "csp.mm"
include "cdiv.mm"
include "h1de2bi.mm"
include "wb.mm"
include "his6.mm"
include "necon3bii.mm"
include "hicli.mm"
include "divclzi.mm"
include "sylbir.mm"
include "sylan.mm"
include "ex.mm"
include "sylbid.mm"
include "pm2.61ine.mm"
include "csh.mm"
include "wss.mm"
include "cch.mm"
include "snssi.mm"
include "occl.mm"
include "mp2b.mm"
include "choccli.mm"
include "chshii.mm"
include "h1did.mm"
include "shmulcl.mm"
include "mp3an13.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "impbii.mm"

theorem h1de2ctlem
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume h1de2.1: |- A e. ~H
  assume h1de2.2: |- B e. ~H

  disjoint A x
  disjoint B x
  assert |- ( A e. ( _|_ ` ( _|_ ` { B } ) ) <-> E. x e. CC A = ( x .h B ) )

  proof
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
    vx
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    @3
    @7
    wi
    cB
    c0v
    cB
    c0v
    wceq
    #
    @3
    cA
    cc0
    cB
    csm
    co
    #
    wceq
    #
    @7
    @8
    @3
    cA
    c0v
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
    @10
    @8
    @2
    @13
    cA
    @8
    @1
    @12
    cort
    @8
    @0
    @11
    cort
    cB
    c0v
    sneq
    fveq2d
    fveq2d
    eleq2d
    cA
    @11
    wcel
    cA
    c0v
    wceq
    @14
    @10
    cA
    c0v
    cA
    chil
    h1de2.1
    elexi
    elsn
    @13
    @11
    cA
    @11
    hsn0elch
    ococi
    eleq2i
    @9
    c0v
    cA
    cB
    chil
    wcel
    #
    @9
    c0v
    wceq
    h1de2.2
    cB
    ax-hvmul0
    ax-mp
    eqeq2i
    3bitr4ri
    syl6rbbr
    cc0
    cc
    wcel
    @10
    @7
    0cn
    @6
    @10
    vx
    cc0
    cc
    @4
    cc0
    wceq
    @5
    @9
    cA
    @4
    cc0
    cB
    csm
    oveq1
    eqeq2d
    rspcev
    mpan
    syl6bir
    cB
    c0v
    wne
    #
    @3
    cA
    cA
    cB
    csp
    co
    #
    cB
    cB
    csp
    co
    #
    cdiv
    co
    #
    cB
    csm
    co
    #
    wceq
    #
    @7
    cA
    cB
    h1de2.1
    h1de2.2
    h1de2bi
    @16
    @21
    @7
    @16
    @19
    cc
    wcel
    #
    @21
    @7
    @16
    @18
    cc0
    wne
    @22
    @18
    cc0
    cB
    c0v
    @15
    @18
    cc0
    wceq
    @8
    wb
    h1de2.2
    cB
    his6
    ax-mp
    necon3bii
    @17
    @18
    cA
    cB
    h1de2.1
    h1de2.2
    hicli
    cB
    cB
    h1de2.2
    h1de2.2
    hicli
    divclzi
    sylbir
    @6
    @21
    vx
    @19
    cc
    @4
    @19
    wceq
    @5
    @20
    cA
    @4
    @19
    cB
    csm
    oveq1
    eqeq2d
    rspcev
    sylan
    ex
    sylbid
    pm2.61ine
    @6
    @3
    vx
    cc
    @4
    cc
    wcel
    #
    @3
    @6
    @5
    @2
    wcel
    #
    @2
    csh
    wcel
    @23
    cB
    @2
    wcel
    #
    @24
    @2
    @1
    @15
    @0
    chil
    wss
    @1
    cch
    wcel
    h1de2.2
    cB
    chil
    snssi
    @0
    occl
    mp2b
    choccli
    chshii
    @15
    @25
    h1de2.2
    cB
    h1did
    ax-mp
    @4
    cB
    @2
    shmulcl
    mp3an13
    cA
    @5
    @2
    eleq1
    syl5ibrcom
    rexlimiv
    impbii
end
