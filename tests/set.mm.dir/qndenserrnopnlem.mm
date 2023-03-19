include "cv.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "wcel.mm"
include "cq.mm"
include "cmap.mm"
include "cr.mm"
include "cxmt.mm"
include "cmopn.mm"
include "cme.mm"
include "cfn.mm"
include "rrxmetfi.mm"
include "syl.mm"
include "metxmet.mm"
include "crrx.mm"
include "ctopn.mm"
include "syl6eleq.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "rrxtopnfi.mm"
include "cds.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "rrxdsfi.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "mopni2.mm"
include "syl3anc.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "ctopon.mm"
include "cbs.mm"
include "ctps.mm"
include "rrxtps.mm"
include "istps.mm"
include "sylib.mm"
include "rrxbasefi.mm"
include "toponss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "simp2.mm"
include "qndenserrnbl.mm"
include "wi.mm"
include "ssel.mm"
include "adantr.mm"
include "3ad2antl3.mm"
include "reximdva.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdv.mm"

theorem qndenserrnopnlem
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  assume qndenserrnopnlem.i: |- ( ph -> I e. Fin )
  assume qndenserrnopnlem.j: |- J = ( TopOpen ` ( RR^ ` I ) )
  assume qndenserrnopnlem.v: |- ( ph -> V e. J )
  assume qndenserrnopnlem.x: |- ( ph -> X e. V )
  assume qndenserrnopnlem.d: |- D = ( dist ` ( RR^ ` I ) )

  disjoint D y
  disjoint I y
  disjoint V y
  disjoint X y
  disjoint ph y
  disjoint D e
  disjoint e y
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint V e
  disjoint X e
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. y e. ( QQ ^m I ) y e. V )

  proof
    wph
    cX
    ve
    cv
    #
    cD
    cbl
    cfv
    co
    #
    cV
    wss
    #
    ve
    crp
    wrex
    #
    vy
    cv
    #
    cV
    wcel
    #
    vy
    cq
    cI
    cmap
    co
    #
    wrex
    #
    wph
    cD
    cr
    cI
    cmap
    co
    #
    cxmt
    cfv
    wcel
    #
    cV
    cD
    cmopn
    cfv
    #
    wcel
    cX
    cV
    wcel
    @3
    wph
    cD
    @8
    cme
    cfv
    wcel
    #
    @9
    wph
    cI
    cfn
    wcel
    #
    @11
    qndenserrnopnlem.i
    cD
    cI
    qndenserrnopnlem.d
    rrxmetfi
    syl
    cD
    @8
    metxmet
    syl
    wph
    cV
    cI
    crrx
    cfv
    #
    ctopn
    cfv
    #
    @10
    wph
    cV
    cJ
    @14
    qndenserrnopnlem.v
    qndenserrnopnlem.j
    syl6eleq
    wph
    @14
    vf
    vg
    @8
    @8
    cI
    vk
    cv
    #
    vf
    cv
    cfv
    @15
    vg
    cv
    cfv
    cmin
    co
    c2
    cexp
    co
    vk
    csu
    csqrt
    cfv
    cmpt2
    #
    cmopn
    cfv
    @10
    wph
    vf
    vg
    vk
    cI
    qndenserrnopnlem.i
    rrxtopnfi
    wph
    @16
    cD
    cmopn
    wph
    cD
    @13
    cds
    cfv
    #
    @16
    cD
    @17
    wceq
    wph
    qndenserrnopnlem.d
    a1i
    wph
    @12
    @17
    @16
    wceq
    qndenserrnopnlem.i
    @8
    vf
    vg
    vk
    @13
    cI
    @13
    eqid
    #
    @8
    eqid
    rrxdsfi
    syl
    eqtr2d
    fveq2d
    eqtrd
    eleqtrd
    qndenserrnopnlem.x
    ve
    cV
    cD
    cX
    @10
    @8
    @10
    eqid
    mopni2
    syl3anc
    wph
    @2
    @7
    ve
    crp
    wph
    @0
    crp
    wcel
    #
    @2
    @7
    wph
    @19
    @2
    w3a
    #
    @4
    @1
    wcel
    #
    vy
    @6
    wrex
    @7
    @20
    vy
    cD
    @0
    cI
    cX
    wph
    @19
    @12
    @2
    qndenserrnopnlem.i
    3ad2ant1
    wph
    @19
    cX
    @8
    wcel
    @2
    wph
    cV
    @8
    cX
    wph
    cJ
    @8
    ctopon
    cfv
    #
    wcel
    cV
    cJ
    wcel
    cV
    @8
    wss
    wph
    cJ
    @13
    cbs
    cfv
    #
    ctopon
    cfv
    #
    @22
    wph
    @13
    ctps
    wcel
    #
    cJ
    @24
    wcel
    wph
    @12
    @25
    qndenserrnopnlem.i
    cI
    cfn
    rrxtps
    syl
    @23
    cJ
    @13
    @23
    eqid
    #
    qndenserrnopnlem.j
    istps
    sylib
    wph
    @23
    @8
    ctopon
    wph
    @23
    @13
    cI
    qndenserrnopnlem.i
    @18
    @26
    rrxbasefi
    fveq2d
    eleqtrd
    qndenserrnopnlem.v
    cV
    cJ
    @8
    toponss
    syl2anc
    qndenserrnopnlem.x
    sseldd
    3ad2ant1
    qndenserrnopnlem.d
    wph
    @19
    @2
    simp2
    qndenserrnbl
    @20
    @21
    @5
    vy
    @6
    @2
    wph
    @4
    @6
    wcel
    #
    @21
    @5
    wi
    #
    @19
    @2
    @28
    @27
    @1
    cV
    @4
    ssel
    adantr
    3ad2antl3
    reximdva
    mpd
    3exp
    rexlimdv
    mpd
end
