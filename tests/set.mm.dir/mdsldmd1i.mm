include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cort.mm"
include "cfv.mm"
include "wb.mm"
include "cch.mm"
include "wcel.mm"
include "mddmd.mm"
include "mp2an.mm"
include "dmdmd.mm"
include "anbi12ci.mm"
include "chincli.mm"
include "chsscon3i.mm"
include "chdmm1i.mm"
include "sseq1i.mm"
include "bitri.mm"
include "chjcli.mm"
include "chdmj1i.mm"
include "incom.mm"
include "eqtri.mm"
include "sseq12i.mm"
include "choccli.mm"
include "mdslmd2i.mm"
include "syl2anb.mm"
include "breq12i.mm"
include "3bitr4g.mm"

theorem mdsldmd1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume mdslmd.1: |- A e. CH
  assume mdslmd.2: |- B e. CH
  assume mdslmd.3: |- C e. CH
  assume mdslmd.4: |- D e. CH


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( A C_ ( C i^i D ) /\ ( C vH D ) C_ ( A vH B ) ) ) -> ( C MH* D <-> ( C i^i B ) MH* ( D i^i B ) ) )

  proof
    cA
    cB
    cmd
    wbr
    #
    cB
    cA
    cdmd
    wbr
    #
    wa
    #
    cA
    cC
    cD
    cin
    #
    wss
    #
    cC
    cD
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    #
    wa
    cC
    cort
    cfv
    #
    cD
    cort
    cfv
    #
    cmd
    wbr
    #
    @9
    cB
    cort
    cfv
    #
    chj
    co
    #
    @10
    @12
    chj
    co
    #
    cmd
    wbr
    #
    cC
    cD
    cdmd
    wbr
    #
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    cdmd
    wbr
    #
    @2
    @12
    cA
    cort
    cfv
    #
    cmd
    wbr
    #
    @20
    @12
    cdmd
    wbr
    #
    wa
    @12
    @20
    cin
    #
    @9
    @10
    cin
    #
    wss
    #
    @9
    @10
    chj
    co
    #
    @20
    wss
    #
    wa
    @11
    @15
    wb
    @8
    @0
    @22
    @1
    @21
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @0
    @22
    wb
    mdslmd.1
    mdslmd.2
    cA
    cB
    mddmd
    mp2an
    @29
    @28
    @1
    @21
    wb
    mdslmd.2
    mdslmd.1
    cB
    cA
    dmdmd
    mp2an
    anbi12ci
    @4
    @27
    @7
    @25
    @4
    @3
    cort
    cfv
    #
    @20
    wss
    @27
    cA
    @3
    mdslmd.1
    cC
    cD
    mdslmd.3
    mdslmd.4
    chincli
    chsscon3i
    @30
    @26
    @20
    cC
    cD
    mdslmd.3
    mdslmd.4
    chdmm1i
    sseq1i
    bitri
    @7
    @6
    cort
    cfv
    #
    @5
    cort
    cfv
    #
    wss
    @25
    @5
    @6
    cC
    cD
    mdslmd.3
    mdslmd.4
    chjcli
    cA
    cB
    mdslmd.1
    mdslmd.2
    chjcli
    chsscon3i
    @31
    @23
    @32
    @24
    @31
    @20
    @12
    cin
    @23
    cA
    cB
    mdslmd.1
    mdslmd.2
    chdmj1i
    @20
    @12
    incom
    eqtri
    cC
    cD
    mdslmd.3
    mdslmd.4
    chdmj1i
    sseq12i
    bitri
    anbi12ci
    @12
    @20
    @9
    @10
    cB
    mdslmd.2
    choccli
    cA
    mdslmd.1
    choccli
    cC
    mdslmd.3
    choccli
    cD
    mdslmd.4
    choccli
    mdslmd2i
    syl2anb
    cC
    cch
    wcel
    cD
    cch
    wcel
    @16
    @11
    wb
    mdslmd.3
    mdslmd.4
    cC
    cD
    dmdmd
    mp2an
    @19
    @17
    cort
    cfv
    #
    @18
    cort
    cfv
    #
    cmd
    wbr
    #
    @15
    @17
    cch
    wcel
    @18
    cch
    wcel
    @19
    @35
    wb
    cC
    cB
    mdslmd.3
    mdslmd.2
    chincli
    cD
    cB
    mdslmd.4
    mdslmd.2
    chincli
    @17
    @18
    dmdmd
    mp2an
    @33
    @13
    @34
    @14
    cmd
    cC
    cB
    mdslmd.3
    mdslmd.2
    chdmm1i
    cD
    cB
    mdslmd.4
    mdslmd.2
    chdmm1i
    breq12i
    bitri
    3bitr4g
end
