include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cv.mm"
include "cminusg.mm"
include "cmpt.mm"
include "c0g.mm"
include "ccom.mm"
include "eqidd.mm"
include "cgrp.mm"
include "wf.mm"
include "cmnd.mm"
include "wss.mm"
include "grpmnd.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prds0g.mm"
include "prdsmndd.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cvv.mm"
include "eqid.mm"
include "elex.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "prdsinvlem.mm"
include "simpld.mm"
include "simprd.mm"
include "isgrpd2.mm"

theorem prdsgrpd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let cB: class B
  let vx: setvar x
  let vb: setvar b
  let va: setvar a
  let cX: class X
  assume prdsgrpd.y: |- Y = ( S Xs_ R )
  assume prdsgrpd.i: |- ( ph -> I e. W )
  assume prdsgrpd.s: |- ( ph -> S e. V )
  assume prdsgrpd.r: |- ( ph -> R : I --> Grp )


  assert |- ( ph -> Y e. Grp )

  proof
    wph
    va
    cY
    cbs
    cfv
    #
    cY
    cplusg
    cfv
    #
    cY
    vb
    cI
    vb
    cv
    #
    va
    cv
    #
    cfv
    @2
    cR
    cfv
    cminusg
    cfv
    cfv
    cmpt
    #
    c0g
    cR
    ccom
    #
    wph
    @0
    eqidd
    wph
    @1
    eqidd
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
    #
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
    @3
    grpmnd
    ssriv
    cI
    cgrp
    cmnd
    cR
    fss
    sylancl
    #
    prds0g
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
    @7
    prdsmndd
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @4
    @0
    wcel
    #
    @4
    @3
    @1
    co
    @5
    wceq
    #
    @9
    vb
    @0
    @1
    cR
    cS
    @3
    cI
    @4
    cvv
    cvv
    cY
    @5
    prdsgrpd.y
    @0
    eqid
    @1
    eqid
    wph
    cS
    cvv
    wcel
    #
    @8
    wph
    cS
    cV
    wcel
    @12
    prdsgrpd.s
    cS
    cV
    elex
    syl
    adantr
    wph
    cI
    cvv
    wcel
    #
    @8
    wph
    cI
    cW
    wcel
    @13
    prdsgrpd.i
    cI
    cW
    elex
    syl
    adantr
    wph
    @6
    @8
    prdsgrpd.r
    adantr
    wph
    @8
    simpr
    @5
    eqid
    @4
    eqid
    prdsinvlem
    #
    simpld
    @9
    @10
    @11
    @14
    simprd
    isgrpd2
end
