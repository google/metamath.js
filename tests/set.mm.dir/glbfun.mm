include "cvv.mm"
include "wcel.mm"
include "wfun.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cab.mm"
include "cres.mm"
include "funmpt.mm"
include "funres.mm"
include "ax-mp.mm"
include "eqid.mm"
include "biid.mm"
include "id.mm"
include "glbfval.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "wn.mm"
include "c0.mm"
include "fun0.mm"
include "cglb.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "pm2.61i.mm"

theorem glbfun
  let cG: class G
  let cK: class K
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume glbfun.g: |- G = ( glb ` K )


  assert |- Fun G

  proof
    cK
    cvv
    wcel
    #
    cG
    wfun
    #
    @0
    @1
    vs
    cK
    cbs
    cfv
    #
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    vy
    vs
    cv
    #
    wral
    vz
    cv
    #
    @5
    @6
    wbr
    vy
    @7
    wral
    @8
    @4
    @6
    wbr
    wi
    vz
    @2
    wral
    wa
    #
    vx
    @2
    crio
    #
    cmpt
    #
    @9
    vx
    @2
    wreu
    vs
    cab
    #
    cres
    #
    wfun
    #
    @11
    wfun
    @14
    vs
    @3
    @10
    funmpt
    @12
    @11
    funres
    ax-mp
    @0
    cG
    @13
    @0
    @9
    vx
    vy
    vz
    @2
    cG
    cK
    @6
    cvv
    vs
    @2
    eqid
    @6
    eqid
    glbfun.g
    @9
    biid
    @0
    id
    glbfval
    funeqd
    mpbiri
    @0
    wn
    #
    @1
    c0
    wfun
    fun0
    @15
    cG
    c0
    @15
    cG
    cK
    cglb
    cfv
    c0
    glbfun.g
    cK
    cglb
    fvprc
    syl5eq
    funeqd
    mpbiri
    pm2.61i
end
