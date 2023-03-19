include "co.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wfun.mm"
include "chom.mm"
include "cfv.mm"
include "cxp.mm"
include "wss.mm"
include "eqid.mm"
include "invss.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "csect.mm"
include "ccat.mm"
include "wcel.mm"
include "adantr.mm"
include "isinv.mm"
include "simplbda.mm"
include "adantrr.mm"
include "simprbda.mm"
include "adantrl.mm"
include "sectcan.mm"
include "ex.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "dffun2.mm"
include "sylanbrc.mm"

theorem invfun
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cN: class N
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  let cS: class S
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )


  assert |- ( ph -> Fun ( X N Y ) )

  proof
    wph
    cX
    cY
    cN
    co
    #
    wrel
    #
    vf
    cv
    #
    vg
    cv
    #
    @0
    wbr
    #
    @2
    vh
    cv
    #
    @0
    wbr
    #
    wa
    #
    vg
    vh
    weq
    #
    wi
    #
    vh
    wal
    #
    vg
    wal
    vf
    wal
    @0
    wfun
    wph
    @0
    cX
    cY
    cC
    chom
    cfv
    #
    co
    #
    cY
    cX
    @11
    co
    #
    cxp
    #
    wss
    @14
    wrel
    @1
    wph
    cB
    cC
    @11
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @11
    eqid
    invss
    @12
    @13
    relxp
    @0
    @14
    relss
    mpisyl
    wph
    @10
    vf
    vg
    wph
    @9
    vh
    wph
    @7
    @8
    wph
    @7
    wa
    cB
    cC
    cC
    csect
    cfv
    #
    @2
    @3
    @5
    cY
    cX
    invfval.b
    @15
    eqid
    #
    wph
    cC
    ccat
    wcel
    @7
    invfval.c
    adantr
    wph
    cY
    cB
    wcel
    @7
    invfval.y
    adantr
    wph
    cX
    cB
    wcel
    @7
    invfval.x
    adantr
    wph
    @4
    @3
    @2
    cY
    cX
    @15
    co
    #
    wbr
    #
    @6
    wph
    @4
    @2
    @3
    cX
    cY
    @15
    co
    #
    wbr
    @18
    wph
    cB
    cC
    @15
    @2
    @3
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @16
    isinv
    simplbda
    adantrr
    wph
    @6
    @2
    @5
    @19
    wbr
    #
    @4
    wph
    @6
    @20
    @5
    @2
    @17
    wbr
    wph
    cB
    cC
    @15
    @2
    @5
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @16
    isinv
    simprbda
    adantrl
    sectcan
    ex
    alrimiv
    alrimivv
    vf
    vg
    vh
    @0
    dffun2
    sylanbrc
end
