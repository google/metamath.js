include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "zring.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cvv.mm"
include "wne.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "0ne1.mm"
include "fprg.mm"
include "mp3an13.mm"
include "prssi.mm"
include "zringbas.mm"
include "syl6sseq.mm"
include "fssd.mm"
include "wb.mm"
include "fvex.mm"
include "prex.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "crg.mm"
include "cfn.mm"
include "wceq.mm"
include "zringring.mm"
include "prfi.mm"
include "eqid.mm"
include "frlmfibas.mm"
include "eleqtrd.mm"

theorem zlmodzxzel
  let cA: class A
  let cB: class B
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxz.z: |- Z = ( ZZring freeLMod { 0 , 1 } )


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> { <. 0 , A >. , <. 1 , B >. } e. ( Base ` Z ) )

  proof
    cA
    cz
    wcel
    cB
    cz
    wcel
    wa
    #
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    zring
    cbs
    cfv
    #
    cc0
    c1
    cpr
    #
    cmap
    co
    #
    cZ
    cbs
    cfv
    #
    @0
    @1
    @4
    wcel
    #
    @3
    @2
    @1
    wf
    #
    @0
    @3
    cA
    cB
    cpr
    #
    @2
    @1
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    @0
    cc0
    c1
    wne
    @3
    @8
    @1
    wf
    @9
    @10
    c0ex
    1ex
    pm3.2i
    0ne1
    cc0
    c1
    cA
    cB
    cvv
    cvv
    cz
    cz
    fprg
    mp3an13
    @0
    @8
    cz
    @2
    cA
    cB
    cz
    prssi
    zringbas
    syl6sseq
    fssd
    @2
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    wa
    @6
    @7
    wb
    @0
    @11
    @12
    zring
    cbs
    fvex
    cc0
    c1
    prex
    pm3.2i
    @2
    @3
    @1
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    zring
    crg
    wcel
    #
    @3
    cfn
    wcel
    #
    wa
    @4
    @5
    wceq
    @0
    @13
    @14
    zringring
    cc0
    c1
    prfi
    pm3.2i
    zring
    cZ
    @3
    @2
    crg
    zlmodzxz.z
    @2
    eqid
    frlmfibas
    mp1i
    eleqtrd
end
