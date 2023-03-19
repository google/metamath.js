include "cr.mm"
include "wcel.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "csn.mm"
include "wf.mm"
include "ipasslem8.mm"
include "fvconst.mm"
include "mpan.mm"
include "eqtr3d.mm"
include "cc.mm"
include "wb.mm"
include "recn.mm"
include "cnv.mm"
include "phnvi.mm"
include "nvscl.mm"
include "mp3an13.mm"
include "dipcl.mm"
include "syl.mm"
include "mp3an.mm"
include "mulcl.mm"
include "mpan2.mm"
include "subeq0ad.mm"
include "mpbid.mm"

theorem ipasslem9
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem9.a: |- A e. X
  assume ipasslem9.b: |- B e. X


  assert |- ( C e. RR -> ( ( C S A ) P B ) = ( C x. ( A P B ) ) )

  proof
    cC
    cr
    wcel
    #
    cC
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cC
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @2
    @4
    wceq
    #
    @0
    cC
    vw
    cr
    vw
    cv
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @8
    @3
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    @5
    cc0
    vw
    cC
    @12
    @5
    cr
    @13
    @8
    cC
    wceq
    #
    @10
    @2
    @11
    @4
    cmin
    @15
    @9
    @1
    cB
    cP
    @8
    cC
    cA
    cS
    oveq1
    oveq1d
    @8
    cC
    @3
    cmul
    oveq1
    oveq12d
    @13
    eqid
    #
    @2
    @4
    cmin
    ovex
    fvmpt
    cr
    cc0
    csn
    @13
    wf
    @0
    @14
    cc0
    wceq
    vw
    cA
    cB
    cP
    cS
    cU
    @13
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem9.a
    ipasslem9.b
    @16
    ipasslem8
    cr
    cc0
    cC
    @13
    fvconst
    mpan
    eqtr3d
    @0
    cC
    cc
    wcel
    #
    @6
    @7
    wb
    cC
    recn
    @17
    @2
    @4
    @17
    @1
    cX
    wcel
    #
    @2
    cc
    wcel
    #
    cU
    cnv
    wcel
    #
    @17
    cA
    cX
    wcel
    #
    @18
    cU
    ip1i.9
    phnvi
    #
    ipasslem9.a
    cC
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvscl
    mp3an13
    @20
    @18
    cB
    cX
    wcel
    #
    @19
    @22
    ipasslem9.b
    @1
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an13
    syl
    @17
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    @20
    @21
    @23
    @24
    @22
    ipasslem9.a
    ipasslem9.b
    cA
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an
    cC
    @3
    mulcl
    mpan2
    subeq0ad
    syl
    mpbid
end
