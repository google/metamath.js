include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wfo.mm"
include "cv.mm"
include "zring.mm"
include "csn.mm"
include "crsp.mm"
include "cfv.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "cmpt.mm"
include "cqs.mm"
include "cqus.mm"
include "cvv.mm"
include "crg.mm"
include "eqidd.mm"
include "cbs.mm"
include "wceq.mm"
include "zringbas.mm"
include "a1i.mm"
include "eqid.mm"
include "ovexd.mm"
include "zringring.mm"
include "quslem.mm"
include "wb.mm"
include "znbas.mm"
include "syl6eqr.mm"
include "foeq3.mm"
include "syl.mm"
include "mpbid.mm"
include "znzrh2.mm"
include "foeq1.mm"
include "mpbird.mm"

theorem znzrhfo
  let cB: class B
  let cL: class L
  let cN: class N
  let cY: class Y
  let vx: setvar x
  assume znzrhfo.y: |- Y = ( Z/nZ ` N )
  assume znzrhfo.b: |- B = ( Base ` Y )
  assume znzrhfo.2: |- L = ( ZRHom ` Y )


  assert |- ( N e. NN0 -> L : ZZ -onto-> B )

  proof
    cN
    cn0
    wcel
    #
    cz
    cB
    cL
    wfo
    #
    cz
    cB
    vx
    cz
    vx
    cv
    zring
    cN
    csn
    zring
    crsp
    cfv
    #
    cfv
    #
    cqg
    co
    #
    cec
    cmpt
    #
    wfo
    #
    @0
    cz
    cz
    @4
    cqs
    #
    @5
    wfo
    #
    @6
    @0
    vx
    @4
    zring
    zring
    @4
    cqus
    co
    #
    @5
    cz
    cvv
    crg
    @0
    @9
    eqidd
    cz
    zring
    cbs
    cfv
    wceq
    @0
    zringbas
    a1i
    @5
    eqid
    @0
    zring
    @3
    cqg
    ovexd
    zring
    crg
    wcel
    @0
    zringring
    a1i
    quslem
    @0
    @7
    cB
    wceq
    @8
    @6
    wb
    @0
    @7
    cY
    cbs
    cfv
    cB
    @4
    @2
    cN
    cY
    @2
    eqid
    #
    znzrhfo.y
    @4
    eqid
    #
    znbas
    znzrhfo.b
    syl6eqr
    @7
    cB
    cz
    @5
    foeq3
    syl
    mpbid
    @0
    cL
    @5
    wceq
    @1
    @6
    wb
    vx
    @4
    @2
    cL
    cN
    cY
    @10
    @11
    znzrhfo.y
    znzrhfo.2
    znzrh2
    cz
    cB
    cL
    @5
    foeq1
    syl
    mpbird
end
