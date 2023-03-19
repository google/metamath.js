include "cv.mm"
include "cch.mm"
include "wcel.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wi.mm"
include "c0h.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "oveq1d.mm"
include "ineq1d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "h0elch.mm"
include "elimel.mm"
include "mdslmd1lem1.mm"
include "dedth.mm"
include "imp.mm"

theorem mdslmd1lem3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume mdslmd.1: |- A e. CH
  assume mdslmd.2: |- B e. CH
  assume mdslmd.3: |- C e. CH
  assume mdslmd.4: |- D e. CH

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( ( x e. CH /\ ( ( A MH B /\ B MH* A ) /\ ( ( A C_ C /\ A C_ D ) /\ ( C C_ ( A vH B ) /\ D C_ ( A vH B ) ) ) ) ) -> ( ( ( x vH A ) C_ D -> ( ( ( x vH A ) vH C ) i^i D ) C_ ( ( x vH A ) vH ( C i^i D ) ) ) -> ( ( ( ( C i^i B ) i^i ( D i^i B ) ) C_ x /\ x C_ ( D i^i B ) ) -> ( ( x vH ( C i^i B ) ) i^i ( D i^i B ) ) C_ ( x vH ( ( C i^i B ) i^i ( D i^i B ) ) ) ) ) )

  proof
    vx
    cv
    #
    cch
    wcel
    #
    cA
    cB
    cmd
    wbr
    cB
    cA
    cdmd
    wbr
    wa
    cA
    cC
    wss
    cA
    cD
    wss
    wa
    cC
    cA
    cB
    chj
    co
    #
    wss
    cD
    @2
    wss
    wa
    wa
    wa
    #
    @0
    cA
    chj
    co
    #
    cD
    wss
    #
    @4
    cC
    chj
    co
    #
    cD
    cin
    #
    @4
    cC
    cD
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    #
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    cin
    #
    @0
    wss
    #
    @0
    @13
    wss
    #
    wa
    #
    @0
    @12
    chj
    co
    #
    @13
    cin
    #
    @0
    @14
    chj
    co
    #
    wss
    #
    wi
    #
    wi
    #
    @1
    @3
    @23
    wi
    @3
    @1
    @0
    c0h
    cif
    #
    cA
    chj
    co
    #
    cD
    wss
    #
    @25
    cC
    chj
    co
    #
    cD
    cin
    #
    @25
    @8
    chj
    co
    #
    wss
    #
    wi
    #
    @14
    @24
    wss
    #
    @24
    @13
    wss
    #
    wa
    #
    @24
    @12
    chj
    co
    #
    @13
    cin
    #
    @24
    @14
    chj
    co
    #
    wss
    #
    wi
    #
    wi
    #
    wi
    @0
    c0h
    @0
    @24
    wceq
    #
    @23
    @40
    @3
    @41
    @11
    @31
    @22
    @39
    @41
    @5
    @26
    @10
    @30
    @41
    @4
    @25
    cD
    @0
    @24
    cA
    chj
    oveq1
    #
    sseq1d
    @41
    @7
    @28
    @9
    @29
    @41
    @6
    @27
    cD
    @41
    @4
    @25
    cC
    chj
    @42
    oveq1d
    ineq1d
    @41
    @4
    @25
    @8
    chj
    @42
    oveq1d
    sseq12d
    imbi12d
    @41
    @17
    @34
    @21
    @38
    @41
    @15
    @32
    @16
    @33
    @0
    @24
    @14
    sseq2
    @0
    @24
    @13
    sseq1
    anbi12d
    @41
    @19
    @36
    @20
    @37
    @41
    @18
    @35
    @13
    @0
    @24
    @12
    chj
    oveq1
    ineq1d
    @0
    @24
    @14
    chj
    oveq1
    sseq12d
    imbi12d
    imbi12d
    imbi2d
    cA
    cB
    cC
    cD
    @24
    mdslmd.1
    mdslmd.2
    mdslmd.3
    mdslmd.4
    @0
    c0h
    cch
    h0elch
    elimel
    mdslmd1lem1
    dedth
    imp
end
