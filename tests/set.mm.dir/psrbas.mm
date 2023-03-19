include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "cmulr.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "csn.mm"
include "cts.mm"
include "ctopn.mm"
include "cpt.mm"
include "cun.mm"
include "eqid.mm"
include "eqidd.mm"
include "adantr.mm"
include "simpr.mm"
include "psrval.mm"
include "fveq2d.mm"
include "ovex.mm"
include "c1.mm"
include "c9.mm"
include "psrvalstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "ssun1.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "ovprc2.mm"
include "adantl.mm"
include "syl5eq.mm"
include "base0.mm"
include "wne.mm"
include "fvprc.mm"
include "cc0.mm"
include "fczpsrbag.mm"
include "syl.mm"
include "ne0i.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "rabex2.mm"
include "map0.mm"
include "sylanbrc.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem psrbas
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cV: class V
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume psrbas.s: |- S = ( I mPwSer R )
  assume psrbas.k: |- K = ( Base ` R )
  assume psrbas.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume psrbas.b: |- B = ( Base ` S )
  assume psrbas.i: |- ( ph -> I e. V )

  disjoint I f
  disjoint g h
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint D h
  disjoint k x
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint I g
  disjoint I h
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint K g
  disjoint K h
  disjoint K k
  disjoint K x
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph x
  disjoint R g
  disjoint R h
  disjoint R k
  disjoint R x
  disjoint V x
  assert |- ( ph -> B = ( K ^m D ) )

  proof
    wph
    cR
    cvv
    wcel
    #
    cB
    cK
    cD
    cmap
    co
    #
    wceq
    wph
    @0
    wa
    #
    cS
    cbs
    cfv
    #
    cnx
    cbs
    cfv
    @1
    cop
    #
    cnx
    cplusg
    cfv
    cR
    cplusg
    cfv
    #
    cof
    @1
    @1
    cxp
    cres
    #
    cop
    #
    cnx
    cmulr
    cfv
    vg
    vh
    @1
    @1
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
    vg
    cv
    #
    cfv
    @8
    @9
    cmin
    cof
    co
    vh
    cv
    cfv
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    cmpt
    cmpt2
    #
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
    vg
    cK
    @1
    cD
    @9
    csn
    cxp
    @10
    @11
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
    cbs
    cfv
    #
    cB
    @1
    @2
    cS
    @19
    cbs
    @2
    vx
    vy
    @1
    cD
    @5
    @6
    cR
    cS
    @15
    @11
    @12
    vg
    vh
    vf
    vk
    cI
    @17
    cK
    @16
    cV
    cvv
    psrbas.s
    psrbas.k
    @5
    eqid
    @11
    eqid
    @16
    eqid
    psrbas.d
    @2
    @1
    eqidd
    @6
    eqid
    @12
    eqid
    @15
    eqid
    @2
    @17
    eqidd
    wph
    cI
    cV
    wcel
    #
    @0
    psrbas.i
    adantr
    wph
    @0
    simpr
    psrval
    fveq2d
    psrbas.b
    @1
    cvv
    wcel
    @1
    @20
    wceq
    cK
    cD
    cmap
    ovex
    @1
    @19
    cbs
    cvv
    c1
    c9
    cop
    @1
    @6
    cR
    @15
    @12
    @17
    psrvalstr
    baseid
    @4
    csn
    @14
    @19
    @4
    @7
    @13
    snsstp1
    @14
    @18
    ssun1
    sstri
    strfv
    ax-mp
    3eqtr4g
    wph
    @0
    wn
    #
    wa
    #
    cB
    c0
    @1
    @23
    @3
    c0
    cbs
    cfv
    cB
    c0
    @23
    cS
    c0
    cbs
    @23
    cS
    cI
    cR
    cmps
    co
    #
    c0
    psrbas.s
    @22
    @24
    c0
    wceq
    wph
    cI
    cR
    cmps
    reldmpsr
    ovprc2
    adantl
    syl5eq
    fveq2d
    psrbas.b
    base0
    3eqtr4g
    @23
    cK
    c0
    wceq
    cD
    c0
    wne
    #
    @1
    c0
    wceq
    @23
    cK
    cR
    cbs
    cfv
    #
    c0
    psrbas.k
    @22
    @26
    c0
    wceq
    wph
    cR
    cbs
    fvprc
    adantl
    syl5eq
    @23
    vx
    cI
    cc0
    cmpt
    #
    cD
    wcel
    #
    @25
    wph
    @28
    @22
    wph
    @21
    @28
    psrbas.i
    vx
    cD
    vf
    cI
    cV
    psrbas.d
    fczpsrbag
    syl
    adantr
    cD
    @27
    ne0i
    syl
    cK
    cD
    cK
    @26
    cvv
    psrbas.k
    cR
    cbs
    fvex
    eqeltri
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    psrbas.d
    cn0
    cI
    cmap
    ovex
    rabex2
    map0
    sylanbrc
    eqtr4d
    pm2.61dan
end
