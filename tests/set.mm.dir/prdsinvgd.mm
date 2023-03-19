include "cfv.mm"
include "cv.mm"
include "cminusg.mm"
include "cmpt.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "ccom.mm"
include "wcel.mm"
include "cvv.mm"
include "eqid.mm"
include "elex.mm"
include "syl.mm"
include "prdsinvlem.mm"
include "simprd.mm"
include "cgrp.mm"
include "wf.mm"
include "cmnd.mm"
include "wss.mm"
include "grpmnd.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prds0g.mm"
include "eqtrd.mm"
include "wb.mm"
include "prdsgrpd.mm"
include "simpld.mm"
include "grpinvid2.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem prdsinvgd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let va: setvar a
  assume prdsgrpd.y: |- Y = ( S Xs_ R )
  assume prdsgrpd.i: |- ( ph -> I e. W )
  assume prdsgrpd.s: |- ( ph -> S e. V )
  assume prdsgrpd.r: |- ( ph -> R : I --> Grp )
  assume prdsinvgd.b: |- B = ( Base ` Y )
  assume prdsinvgd.n: |- N = ( invg ` Y )
  assume prdsinvgd.x: |- ( ph -> X e. B )

  disjoint B x
  disjoint I x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint X x
  disjoint Y x
  disjoint b x
  disjoint I b
  disjoint a b
  disjoint a x
  disjoint a ph
  disjoint b ph
  disjoint R b
  disjoint S b
  disjoint Y a
  disjoint Y b
  assert |- ( ph -> ( N ` X ) = ( x e. I |-> ( ( invg ` ( R ` x ) ) ` ( X ` x ) ) ) )

  proof
    wph
    cX
    cN
    cfv
    vx
    cI
    vx
    cv
    #
    cX
    cfv
    @0
    cR
    cfv
    cminusg
    cfv
    cfv
    cmpt
    #
    wceq
    #
    @1
    cX
    cY
    cplusg
    cfv
    #
    co
    #
    cY
    c0g
    cfv
    #
    wceq
    #
    wph
    @4
    c0g
    cR
    ccom
    #
    @5
    wph
    @1
    cB
    wcel
    #
    @4
    @7
    wceq
    #
    wph
    vx
    cB
    @3
    cR
    cS
    cX
    cI
    @1
    cvv
    cvv
    cY
    @7
    prdsgrpd.y
    prdsinvgd.b
    @3
    eqid
    #
    wph
    cS
    cV
    wcel
    cS
    cvv
    wcel
    prdsgrpd.s
    cS
    cV
    elex
    syl
    wph
    cI
    cW
    wcel
    cI
    cvv
    wcel
    prdsgrpd.i
    cI
    cW
    elex
    syl
    prdsgrpd.r
    prdsinvgd.x
    @7
    eqid
    @1
    eqid
    prdsinvlem
    #
    simprd
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdsgrpd.y
    prdsgrpd.i
    prdsgrpd.s
    wph
    cI
    cgrp
    cR
    wf
    cgrp
    cmnd
    wss
    cI
    cmnd
    cR
    wf
    prdsgrpd.r
    va
    cgrp
    cmnd
    va
    cv
    grpmnd
    ssriv
    cI
    cgrp
    cmnd
    cR
    fss
    sylancl
    prds0g
    eqtrd
    wph
    cY
    cgrp
    wcel
    cX
    cB
    wcel
    @8
    @2
    @6
    wb
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdsgrpd.y
    prdsgrpd.i
    prdsgrpd.s
    prdsgrpd.r
    prdsgrpd
    prdsinvgd.x
    wph
    @8
    @9
    @11
    simpld
    cB
    @3
    cY
    cN
    cX
    @1
    @5
    prdsinvgd.b
    @10
    @5
    eqid
    prdsinvgd.n
    grpinvid2
    syl3anc
    mpbird
end
