include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cima.mm"
include "wss.mm"
include "clm.mm"
include "wbr.mm"
include "cflf.mm"
include "co.mm"
include "wfn.mm"
include "wb.mm"
include "cpw.mm"
include "uzf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "wceq.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rexima.mm"
include "mp2an.mm"
include "wfun.mm"
include "cdm.mm"
include "simpl3.mm"
include "ffun.mm"
include "syl.mm"
include "uzss.mm"
include "eleq2s.mm"
include "adantl.mm"
include "fdm.mm"
include "syl6eq.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "rexbidva.mm"
include "syl5rbb.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqidd.mm"
include "lmbrf.mm"
include "cfbas.mm"
include "uzfbas.mm"
include "flffbas.mm"
include "syl3an2.mm"
include "3bitr4d.mm"

theorem lmflf
  let cP: class P
  let cF: class F
  let cJ: class J
  let cL: class L
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume lmflf.1: |- Z = ( ZZ>= ` M )
  assume lmflf.2: |- L = ( Z filGen ( ZZ>= " Z ) )


  assert |- ( ( J e. ( TopOn ` X ) /\ M e. ZZ /\ F : Z --> X ) -> ( F ( ~~>t ` J ) P <-> P e. ( ( J fLimf L ) ` F ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cZ
    cX
    cF
    wf
    #
    w3a
    #
    cP
    cX
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @5
    wcel
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vx
    cJ
    wral
    #
    wa
    @4
    @6
    cF
    vy
    cv
    #
    cima
    #
    @5
    wss
    #
    vy
    cuz
    cZ
    cima
    #
    wrex
    #
    wi
    #
    vx
    cJ
    wral
    #
    wa
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cP
    cF
    cJ
    cL
    cflf
    co
    cfv
    wcel
    #
    @3
    @14
    @21
    @4
    @3
    @13
    @20
    vx
    cJ
    @3
    @12
    @19
    @6
    @19
    cF
    @10
    cima
    #
    @5
    wss
    #
    vj
    cZ
    wrex
    #
    @3
    @12
    cuz
    cz
    wfn
    #
    cZ
    cz
    wss
    @19
    @26
    wb
    cz
    cz
    cpw
    #
    cuz
    wf
    @27
    uzf
    cz
    @28
    cuz
    ffn
    ax-mp
    cZ
    cM
    cuz
    cfv
    #
    cz
    lmflf.1
    cM
    uzssz
    eqsstri
    @17
    @25
    vy
    vj
    cz
    cZ
    cuz
    @15
    @10
    wceq
    @16
    @24
    @5
    @15
    @10
    cF
    imaeq2
    sseq1d
    rexima
    mp2an
    @3
    @25
    @11
    vj
    cZ
    @3
    @9
    cZ
    wcel
    #
    wa
    #
    cF
    wfun
    #
    @10
    cF
    cdm
    #
    wss
    @25
    @11
    wb
    @31
    @2
    @32
    @0
    @1
    @2
    @30
    simpl3
    #
    cZ
    cX
    cF
    ffun
    syl
    @31
    @10
    @29
    @33
    @30
    @10
    @29
    wss
    #
    @3
    @35
    @9
    @29
    cZ
    cM
    @9
    uzss
    lmflf.1
    eleq2s
    adantl
    @31
    @33
    cZ
    @29
    @31
    @2
    @33
    cZ
    wceq
    @34
    cZ
    cX
    cF
    fdm
    syl
    lmflf.1
    syl6eq
    sseqtr4d
    vk
    @10
    @5
    cF
    funimass4
    syl2anc
    rexbidva
    syl5rbb
    imbi2d
    ralbidv
    anbi2d
    @3
    vx
    @8
    cP
    vj
    vk
    cF
    cJ
    cM
    cX
    cZ
    @0
    @1
    @2
    simp1
    lmflf.1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    @7
    cZ
    wcel
    wa
    @8
    eqidd
    lmbrf
    @1
    @0
    @18
    cZ
    cfbas
    cfv
    wcel
    @2
    @23
    @22
    wb
    cM
    cZ
    lmflf.1
    uzfbas
    cP
    @18
    vx
    cF
    cJ
    cL
    cX
    cZ
    vy
    lmflf.2
    flffbas
    syl3an2
    3bitr4d
end
