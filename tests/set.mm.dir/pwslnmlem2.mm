include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "c0g.mm"
include "csn.mm"
include "cima.mm"
include "cress.mm"
include "clnm.mm"
include "crn.mm"
include "clmod.mm"
include "cun.mm"
include "cvv.mm"
include "wss.mm"
include "unex.mm"
include "a1i.mm"
include "ssun1.mm"
include "eqid.mm"
include "pwssplit3.mm"
include "syl3anc.mm"
include "cxp.mm"
include "wceq.mm"
include "crab.mm"
include "fvex.mm"
include "mptiniseg.mm"
include "ax-mp.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "pws0g.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "clmim.mm"
include "clmic.mm"
include "wbr.mm"
include "wb.mm"
include "cin.mm"
include "c0.mm"
include "pwssplit4.mm"
include "brlmici.mm"
include "lnmlmic.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "wfo.mm"
include "pwssplit1.mm"
include "forn.mm"
include "syl.mm"
include "ressid.mm"
include "eqtrd.mm"
include "lmhmlnmsplit.mm"

theorem pwslnmlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume pwslnmlem2.a: |- A e. _V
  assume pwslnmlem2.b: |- B e. _V
  assume pwslnmlem2.x: |- X = ( W ^s A )
  assume pwslnmlem2.y: |- Y = ( W ^s B )
  assume pwslnmlem2.z: |- Z = ( W ^s ( A u. B ) )
  assume pwslnmlem2.w: |- ( ph -> W e. LMod )
  assume pwslnmlem2.dj: |- ( ph -> ( A i^i B ) = (/) )
  assume pwslnmlem2.xn: |- ( ph -> X e. LNoeM )
  assume pwslnmlem2.yn: |- ( ph -> Y e. LNoeM )


  assert |- ( ph -> Z e. LNoeM )

  proof
    wph
    vx
    cZ
    cbs
    cfv
    #
    vx
    cv
    cA
    cres
    #
    cmpt
    #
    cZ
    cX
    clmhm
    co
    wcel
    #
    cZ
    @2
    ccnv
    cX
    c0g
    cfv
    #
    csn
    cima
    #
    cress
    co
    #
    clnm
    wcel
    cX
    @2
    crn
    #
    cress
    co
    #
    clnm
    wcel
    cZ
    clnm
    wcel
    wph
    cW
    clmod
    wcel
    #
    cA
    cB
    cun
    #
    cvv
    wcel
    #
    cA
    @10
    wss
    #
    @3
    pwslnmlem2.w
    @11
    wph
    cA
    cB
    pwslnmlem2.a
    pwslnmlem2.b
    unex
    a1i
    #
    @12
    wph
    cA
    cB
    ssun1
    a1i
    #
    vx
    @0
    cX
    cbs
    cfv
    #
    @10
    @2
    cA
    cW
    cvv
    cZ
    cX
    pwslnmlem2.z
    pwslnmlem2.x
    @0
    eqid
    #
    @15
    eqid
    #
    @2
    eqid
    #
    pwssplit3
    syl3anc
    wph
    @6
    cZ
    @1
    cA
    cW
    c0g
    cfv
    #
    csn
    cxp
    #
    wceq
    #
    vx
    @0
    crab
    #
    cress
    co
    #
    clnm
    wph
    @5
    @22
    cZ
    cress
    wph
    @5
    @1
    @4
    wceq
    #
    vx
    @0
    crab
    #
    @22
    @4
    cvv
    wcel
    @5
    @25
    wceq
    cX
    c0g
    fvex
    vx
    @0
    @1
    @4
    @2
    cvv
    @18
    mptiniseg
    ax-mp
    wph
    @24
    @21
    vx
    @0
    wph
    @4
    @20
    @1
    wph
    @20
    @4
    wph
    cW
    cmnd
    wcel
    #
    cA
    cvv
    wcel
    @20
    @4
    wceq
    wph
    @9
    cW
    cgrp
    wcel
    @26
    pwslnmlem2.w
    cW
    lmodgrp
    cW
    grpmnd
    3syl
    #
    pwslnmlem2.a
    cW
    cA
    cvv
    cX
    @19
    pwslnmlem2.x
    @19
    eqid
    #
    pws0g
    sylancl
    eqcomd
    eqeq2d
    rabbidv
    syl5eq
    oveq2d
    wph
    @23
    clnm
    wcel
    #
    cY
    clnm
    wcel
    #
    pwslnmlem2.yn
    wph
    vy
    @22
    vy
    cv
    cB
    cres
    cmpt
    #
    @23
    cY
    clmim
    co
    wcel
    #
    @23
    cY
    clmic
    wbr
    @29
    @30
    wb
    wph
    @9
    @11
    cA
    cB
    cin
    c0
    wceq
    @32
    pwslnmlem2.w
    @13
    pwslnmlem2.dj
    vy
    vx
    cA
    cB
    cX
    cY
    cW
    cZ
    @31
    @0
    @22
    @23
    cvv
    @19
    pwslnmlem2.z
    @16
    @28
    @22
    eqid
    @31
    eqid
    pwslnmlem2.x
    pwslnmlem2.y
    @23
    eqid
    pwssplit4
    syl3anc
    @23
    cY
    @31
    brlmici
    @23
    cY
    lnmlmic
    3syl
    mpbird
    eqeltrd
    wph
    @8
    cX
    clnm
    wph
    @8
    cX
    @15
    cress
    co
    #
    cX
    wph
    @7
    @15
    cX
    cress
    wph
    @0
    @15
    @2
    wfo
    #
    @7
    @15
    wceq
    wph
    @26
    @11
    @12
    @34
    @27
    @13
    @14
    vx
    @0
    @15
    @10
    @2
    cA
    cW
    cvv
    cZ
    cX
    pwslnmlem2.z
    pwslnmlem2.x
    @16
    @17
    @18
    pwssplit1
    syl3anc
    @0
    @15
    @2
    forn
    syl
    oveq2d
    wph
    cX
    clnm
    wcel
    @33
    cX
    wceq
    pwslnmlem2.xn
    @15
    cX
    clnm
    @17
    ressid
    syl
    eqtrd
    pwslnmlem2.xn
    eqeltrd
    cZ
    cX
    @6
    @2
    @5
    @8
    @4
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @8
    eqid
    lmhmlnmsplit
    syl3anc
end
