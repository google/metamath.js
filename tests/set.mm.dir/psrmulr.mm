include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cmulr.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "csn.mm"
include "cxp.mm"
include "cts.mm"
include "ctopn.mm"
include "cpt.mm"
include "cun.mm"
include "eqid.mm"
include "simpl.mm"
include "psrbas.mm"
include "psrplusg.mm"
include "eqidd.mm"
include "simpr.mm"
include "psrval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "c1.mm"
include "c9.mm"
include "psrvalstr.mm"
include "mulrid.mm"
include "snsstp3.mm"
include "ssun1.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "mpt20.mm"
include "str0.mm"
include "eqtr2i.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "ovprc.mm"
include "syl5eq.mm"
include "base0.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem psrmulr
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let cI: class I
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cX: class X
  assume psrmulr.s: |- S = ( I mPwSer R )
  assume psrmulr.b: |- B = ( Base ` S )
  assume psrmulr.m: |- .x. = ( .r ` R )
  assume psrmulr.t: |- .xb = ( .r ` S )
  assume psrmulr.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }

  disjoint f g
  disjoint f k
  disjoint f x
  disjoint B f
  disjoint g k
  disjoint g x
  disjoint B g
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint f y
  disjoint D f
  disjoint g y
  disjoint D g
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint f h
  disjoint I f
  disjoint g h
  disjoint I g
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint I h
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. k
  disjoint .x. x
  disjoint R f
  disjoint R g
  disjoint R k
  disjoint R x
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph x
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F x
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G x
  disjoint X k
  disjoint X x
  disjoint X y
  assert |- .xb = ( f e. B , g e. B |-> ( k e. D |-> ( R gsum ( x e. { y e. D | y oR <_ k } |-> ( ( f ` x ) .x. ( g ` ( k oF - x ) ) ) ) ) ) )

  proof
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    c.xb
    vf
    vg
    cB
    cB
    vk
    cD
    cR
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    vy
    cD
    crab
    vx
    cv
    #
    vf
    cv
    #
    cfv
    @3
    @4
    cmin
    cof
    co
    vg
    cv
    cfv
    c.x
    co
    cmpt
    cgsu
    co
    cmpt
    #
    cmpt2
    #
    wceq
    @2
    cS
    cmulr
    cfv
    #
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cplusg
    cfv
    cS
    cplusg
    cfv
    #
    cop
    #
    cnx
    cmulr
    cfv
    #
    @7
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    cR
    cop
    cnx
    cvsca
    cfv
    vx
    vf
    cR
    cbs
    cfv
    #
    cB
    cD
    @4
    csn
    cxp
    @5
    c.x
    cof
    co
    cmpt2
    #
    cop
    cnx
    cts
    cfv
    cD
    cR
    ctopn
    cfv
    #
    csn
    cxp
    cpt
    cfv
    #
    cop
    ctp
    #
    cun
    #
    cmulr
    cfv
    #
    c.xb
    @7
    @2
    cS
    @20
    cmulr
    @2
    vx
    vy
    cB
    cD
    cR
    cplusg
    cfv
    #
    @10
    cR
    cS
    @16
    c.x
    @7
    vf
    vg
    vh
    vk
    cI
    @18
    @15
    @17
    cvv
    cvv
    psrmulr.s
    @15
    eqid
    #
    @22
    eqid
    #
    psrmulr.m
    @17
    eqid
    psrmulr.d
    @2
    cB
    cD
    cR
    cS
    vh
    cI
    @15
    cvv
    psrmulr.s
    @23
    psrmulr.d
    psrmulr.b
    @0
    @1
    simpl
    #
    psrbas
    cB
    @22
    @10
    cR
    cS
    cI
    psrmulr.s
    psrmulr.b
    @24
    @10
    eqid
    psrplusg
    @7
    eqid
    @16
    eqid
    @2
    @18
    eqidd
    @25
    @0
    @1
    simpr
    psrval
    fveq2d
    psrmulr.t
    @7
    cvv
    wcel
    @7
    @21
    wceq
    vf
    vg
    cB
    cB
    @6
    cB
    cS
    cbs
    cfv
    #
    cvv
    psrmulr.b
    cS
    cbs
    fvex
    eqeltri
    #
    @27
    mpt2ex
    @7
    @20
    cmulr
    cvv
    c1
    c9
    cop
    cB
    @10
    cR
    @16
    @7
    @18
    psrvalstr
    mulrid
    @13
    csn
    @14
    @20
    @9
    @11
    @13
    snsstp3
    @14
    @19
    ssun1
    sstri
    strfv
    ax-mp
    3eqtr4g
    @2
    wn
    #
    c0
    cmulr
    cfv
    #
    vf
    vg
    c0
    c0
    @6
    cmpt2
    #
    c.xb
    @7
    @30
    c0
    @29
    vf
    vg
    c0
    @6
    mpt20
    cmulr
    @12
    mulrid
    str0
    eqtr2i
    @28
    c.xb
    @8
    @29
    psrmulr.t
    @28
    cS
    c0
    cmulr
    @28
    cS
    cI
    cR
    cmps
    co
    c0
    psrmulr.s
    cI
    cR
    cmps
    reldmpsr
    ovprc
    syl5eq
    #
    fveq2d
    syl5eq
    @28
    cB
    c0
    wceq
    #
    @32
    @7
    @30
    wceq
    @28
    @26
    c0
    cbs
    cfv
    cB
    c0
    @28
    cS
    c0
    cbs
    @31
    fveq2d
    psrmulr.b
    base0
    3eqtr4g
    #
    @33
    vf
    vg
    cB
    cB
    c0
    c0
    @6
    mpt2eq12
    syl2anc
    3eqtr4a
    pm2.61i
end
