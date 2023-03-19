include "crn.mm"
include "csigagen.mm"
include "cfv.mm"
include "cbrsiga.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "ctx.mm"
include "co.mm"
include "csx.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "cr.mm"
include "dya2iocucvr.mm"
include "br2base.mm"
include "eqtr4i.mm"
include "csiga.mm"
include "brsigarn.mm"
include "elexi.mm"
include "mpt2ex.mm"
include "rnex.mm"
include "wa.mm"
include "coprab.mm"
include "dya2icobrsiga.mm"
include "sseli.mm"
include "anim12i.mm"
include "anim1i.mm"
include "ssoprab2i.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "cbvmpt2v.mm"
include "3sstr4i.mm"
include "rnss.mm"
include "ax-mp.mm"
include "sssigagen2.mm"
include "mp2an.mm"
include "sigagenss2.mm"
include "mp3an.mm"
include "sxbrsigalem4.mm"
include "eqid.mm"
include "sxval.mm"

theorem sxbrsigalem5
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint n u
  disjoint n v
  disjoint n x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint I u
  disjoint I v
  disjoint R n
  disjoint R x
  disjoint J u
  disjoint J x
  disjoint J v
  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint n u
  disjoint n v
  disjoint R n
  disjoint R x
  disjoint J x
  disjoint e f
  disjoint e g
  disjoint e n
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint f g
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint n y
  disjoint u y
  disjoint v y
  disjoint x y
  disjoint R y
  assert |- ( sigaGen ` ( J tX J ) ) C_ ( BrSiga sX BrSiga )

  proof
    cR
    crn
    #
    csigagen
    cfv
    #
    ve
    vf
    cbrsiga
    cbrsiga
    ve
    cv
    #
    vf
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    csigagen
    cfv
    #
    cJ
    cJ
    ctx
    co
    csigagen
    cfv
    cbrsiga
    cbrsiga
    csx
    co
    #
    @0
    cuni
    #
    @6
    cuni
    #
    wceq
    @0
    @7
    wss
    #
    @6
    cvv
    wcel
    #
    @1
    @7
    wss
    @9
    cr
    cr
    cxp
    @10
    vx
    vv
    vu
    cR
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocucvr
    ve
    vf
    br2base
    eqtr4i
    @12
    @0
    @6
    wss
    #
    @11
    @5
    ve
    vf
    cbrsiga
    cbrsiga
    @4
    cbrsiga
    cr
    csiga
    cfv
    #
    brsigarn
    elexi
    #
    @15
    mpt2ex
    rnex
    #
    cR
    @5
    wss
    @13
    vu
    cv
    #
    cI
    crn
    #
    wcel
    #
    vv
    cv
    #
    @18
    wcel
    #
    wa
    #
    vg
    cv
    @17
    @20
    cxp
    #
    wceq
    #
    wa
    #
    vu
    vv
    vg
    coprab
    #
    @17
    cbrsiga
    wcel
    #
    @20
    cbrsiga
    wcel
    #
    wa
    #
    @24
    wa
    #
    vu
    vv
    vg
    coprab
    #
    cR
    @5
    @25
    @30
    vu
    vv
    vg
    @22
    @29
    @24
    @19
    @27
    @21
    @28
    @18
    cbrsiga
    @17
    vx
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2icobrsiga
    #
    sseli
    @18
    cbrsiga
    @20
    @32
    sseli
    anim12i
    anim1i
    ssoprab2i
    cR
    vu
    vv
    @18
    @18
    @23
    cmpt2
    @26
    dya2ioc.2
    vu
    vv
    vg
    @18
    @18
    @23
    df-mpt2
    eqtri
    @5
    vu
    vv
    cbrsiga
    cbrsiga
    @23
    cmpt2
    @31
    ve
    vf
    vu
    vv
    cbrsiga
    cbrsiga
    @4
    @23
    @17
    @3
    cxp
    @2
    @17
    @3
    xpeq1
    @3
    @20
    @17
    xpeq2
    cbvmpt2v
    vu
    vv
    vg
    cbrsiga
    cbrsiga
    @23
    df-mpt2
    eqtri
    3sstr4i
    cR
    @5
    rnss
    ax-mp
    @6
    @0
    cvv
    sssigagen2
    mp2an
    @16
    @0
    @6
    cvv
    sigagenss2
    mp3an
    vx
    vv
    vu
    cR
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    sxbrsigalem4
    cbrsiga
    @14
    wcel
    #
    @33
    @8
    @7
    wceq
    brsigarn
    brsigarn
    ve
    vf
    @6
    cbrsiga
    cbrsiga
    @14
    @14
    @6
    eqid
    sxval
    mp2an
    3sstr4i
end
