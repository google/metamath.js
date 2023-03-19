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
include "ineq1.mm"
include "sseq1d.mm"
include "oveq1d.mm"
include "ineq1d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "oveq1.mm"
include "imbi2d.mm"
include "h0elch.mm"
include "elimel.mm"
include "mdslmd1lem2.mm"
include "dedth.mm"
include "imp.mm"

theorem mdslmd1lem4
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
  assert |- ( ( x e. CH /\ ( ( A MH B /\ B MH* A ) /\ ( ( A C_ C /\ A C_ D ) /\ ( C C_ ( A vH B ) /\ D C_ ( A vH B ) ) ) ) ) -> ( ( ( x i^i B ) C_ ( D i^i B ) -> ( ( ( x i^i B ) vH ( C i^i B ) ) i^i ( D i^i B ) ) C_ ( ( x i^i B ) vH ( ( C i^i B ) i^i ( D i^i B ) ) ) ) -> ( ( ( C i^i D ) C_ x /\ x C_ D ) -> ( ( x vH C ) i^i D ) C_ ( x vH ( C i^i D ) ) ) ) )

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
    cB
    cin
    #
    cD
    cB
    cin
    #
    wss
    #
    @4
    cC
    cB
    cin
    #
    chj
    co
    #
    @5
    cin
    #
    @4
    @7
    @5
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
    cD
    cin
    #
    @0
    wss
    #
    @0
    cD
    wss
    #
    wa
    #
    @0
    cC
    chj
    co
    #
    cD
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
    cB
    cin
    #
    @5
    wss
    #
    @25
    @7
    chj
    co
    #
    @5
    cin
    #
    @25
    @10
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
    cD
    wss
    #
    wa
    #
    @24
    cC
    chj
    co
    #
    cD
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
    @13
    @31
    @22
    @39
    @41
    @6
    @26
    @12
    @30
    @41
    @4
    @25
    @5
    @0
    @24
    cB
    ineq1
    #
    sseq1d
    @41
    @9
    @28
    @11
    @29
    @41
    @8
    @27
    @5
    @41
    @4
    @25
    @7
    chj
    @42
    oveq1d
    ineq1d
    @41
    @4
    @25
    @10
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
    cD
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
    cD
    @0
    @24
    cC
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
    mdslmd1lem2
    dedth
    imp
end
