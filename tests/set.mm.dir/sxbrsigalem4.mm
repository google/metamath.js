include "ctx.mm"
include "co.mm"
include "csigagen.mm"
include "cfv.mm"
include "crn.mm"
include "sxbrsigalem1.mm"
include "ccld.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "cxp.mm"
include "cmpt.mm"
include "cun.mm"
include "sxbrsigalem2.mm"
include "sxbrsigalem3.mm"
include "sstri.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "ctop.mm"
include "wcel.mm"
include "tpr2tp.mm"
include "topontopi.mm"
include "eqid.mm"
include "unicls.mm"
include "cldssbrsiga.mm"
include "ax-mp.mm"
include "sigagenss2.mm"
include "mp3an.mm"
include "eqssi.mm"

theorem sxbrsigalem4
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let ve: setvar e
  let vf: setvar f
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
  disjoint e n
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint n y
  disjoint u y
  disjoint v y
  disjoint x y
  disjoint R y
  assert |- ( sigaGen ` ( J tX J ) ) = ( sigaGen ` ran R )

  proof
    cJ
    cJ
    ctx
    co
    #
    csigagen
    cfv
    #
    cR
    crn
    csigagen
    cfv
    #
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
    sxbrsigalem1
    @2
    @0
    ccld
    cfv
    #
    csigagen
    cfv
    #
    @1
    @2
    ve
    cr
    ve
    cv
    cpnf
    cico
    co
    cr
    cxp
    cmpt
    crn
    vf
    cr
    cr
    vf
    cv
    cpnf
    cico
    co
    cxp
    cmpt
    crn
    cun
    csigagen
    cfv
    @4
    vx
    vv
    vu
    cR
    ve
    vf
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    sxbrsigalem2
    ve
    vf
    cJ
    sxbrsiga.0
    sxbrsigalem3
    sstri
    @3
    cuni
    @0
    cuni
    #
    wceq
    @3
    @1
    wss
    #
    @0
    ctop
    wcel
    #
    @4
    @1
    wss
    @0
    @5
    cr
    cr
    cxp
    @0
    cJ
    sxbrsiga.0
    tpr2tp
    topontopi
    #
    @5
    eqid
    unicls
    @7
    @6
    @8
    @0
    cldssbrsiga
    ax-mp
    @8
    @3
    @0
    ctop
    sigagenss2
    mp3an
    sstri
    eqssi
end
