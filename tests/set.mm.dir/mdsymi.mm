include "cmd.mm"
include "wbr.mm"
include "wb.mm"
include "cort.mm"
include "cfv.mm"
include "c0h.mm"
include "wne.mm"
include "wa.mm"
include "cdmd.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "choccli.mm"
include "eqid.mm"
include "mdsymlem8.mm"
include "cch.mm"
include "wcel.mm"
include "mddmd.mm"
include "mp2an.mm"
include "3bitr4g.mm"
include "wceq.mm"
include "wss.mm"
include "chil.mm"
include "chssii.mm"
include "fveq2.mm"
include "pjococi.mm"
include "choc0.mm"
include "3eqtr3g.mm"
include "syl5sseqr.mm"
include "ssmd1.mm"
include "mp3an12.mm"
include "ssmd2.mm"
include "jca.mm"
include "pm5.1.mm"
include "3syl.mm"
include "pm2.61iine.mm"

theorem mdsymi
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume mdsym.1: |- A e. CH
  assume mdsym.2: |- B e. CH


  assert |- ( A MH B <-> B MH A )

  proof
    cA
    cB
    cmd
    wbr
    #
    cB
    cA
    cmd
    wbr
    #
    wb
    #
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    c0h
    c0h
    @3
    c0h
    wne
    @4
    c0h
    wne
    wa
    @4
    @3
    cdmd
    wbr
    #
    @3
    @4
    cdmd
    wbr
    #
    @0
    @1
    @3
    @4
    @3
    vx
    cv
    chj
    co
    #
    vx
    cB
    mdsym.2
    choccli
    cA
    mdsym.1
    choccli
    @7
    eqid
    mdsymlem8
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @0
    @5
    wb
    mdsym.1
    mdsym.2
    cA
    cB
    mddmd
    mp2an
    @9
    @8
    @1
    @6
    wb
    mdsym.2
    mdsym.1
    cB
    cA
    mddmd
    mp2an
    3bitr4g
    @3
    c0h
    wceq
    #
    cA
    cB
    wss
    #
    @0
    @1
    wa
    #
    @2
    @10
    chil
    cA
    cB
    cA
    mdsym.1
    chssii
    @10
    @3
    cort
    cfv
    c0h
    cort
    cfv
    #
    cB
    chil
    @3
    c0h
    cort
    fveq2
    cB
    mdsym.2
    pjococi
    choc0
    3eqtr3g
    syl5sseqr
    @11
    @0
    @1
    @8
    @9
    @11
    @0
    mdsym.1
    mdsym.2
    cA
    cB
    ssmd1
    mp3an12
    @8
    @9
    @11
    @1
    mdsym.1
    mdsym.2
    cA
    cB
    ssmd2
    mp3an12
    jca
    @0
    @1
    pm5.1
    #
    3syl
    @4
    c0h
    wceq
    #
    cB
    cA
    wss
    #
    @12
    @2
    @15
    chil
    cB
    cA
    cB
    mdsym.2
    chssii
    @15
    @4
    cort
    cfv
    @13
    cA
    chil
    @4
    c0h
    cort
    fveq2
    cA
    mdsym.1
    pjococi
    choc0
    3eqtr3g
    syl5sseqr
    @16
    @0
    @1
    @9
    @8
    @16
    @0
    mdsym.2
    mdsym.1
    cB
    cA
    ssmd2
    mp3an12
    @9
    @8
    @16
    @1
    mdsym.2
    mdsym.1
    cB
    cA
    ssmd1
    mp3an12
    jca
    @14
    3syl
    pm2.61iine
end
