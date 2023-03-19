include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "wral.mm"
include "cntzmhm.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "mpan9.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "mhmf.mm"
include "adantr.mm"
include "ffun.mm"
include "syl.mm"
include "simpr.mm"
include "cntzssv.mm"
include "syl6ss.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cntzmhm2
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cntzmhm.z: |- Z = ( Cntz ` G )
  assume cntzmhm.y: |- Y = ( Cntz ` H )


  assert |- ( ( F e. ( G MndHom H ) /\ S C_ ( Z ` T ) ) -> ( F " S ) C_ ( Y ` ( F " T ) ) )

  proof
    cF
    cG
    cH
    cmhm
    co
    wcel
    #
    cS
    cT
    cZ
    cfv
    #
    wss
    #
    wa
    #
    cF
    cS
    cima
    cF
    cT
    cima
    cY
    cfv
    #
    wss
    #
    vx
    cv
    #
    cF
    cfv
    @4
    wcel
    #
    vx
    cS
    wral
    #
    @0
    @7
    vx
    @1
    wral
    @2
    @8
    @0
    @7
    vx
    @1
    @6
    cT
    cF
    cG
    cH
    cY
    cZ
    cntzmhm.z
    cntzmhm.y
    cntzmhm
    ralrimiva
    @7
    vx
    cS
    @1
    ssralv
    mpan9
    @3
    cF
    wfun
    #
    cS
    cF
    cdm
    #
    wss
    @5
    @8
    wb
    @3
    cG
    cbs
    cfv
    #
    cH
    cbs
    cfv
    #
    cF
    wf
    #
    @9
    @0
    @13
    @2
    @11
    @12
    cG
    cH
    cF
    @11
    eqid
    #
    @12
    eqid
    mhmf
    adantr
    #
    @11
    @12
    cF
    ffun
    syl
    @3
    cS
    @11
    @10
    @3
    cS
    @1
    @11
    @0
    @2
    simpr
    @11
    cT
    cG
    cZ
    @14
    cntzmhm.z
    cntzssv
    syl6ss
    @3
    @13
    @10
    @11
    wceq
    @15
    @11
    @12
    cF
    fdm
    syl
    sseqtr4d
    vx
    cS
    @4
    cF
    funimass4
    syl2anc
    mpbird
end
