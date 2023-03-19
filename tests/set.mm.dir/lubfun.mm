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
include "lubfval.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "wn.mm"
include "c0.mm"
include "fun0.mm"
include "club.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "pm2.61i.mm"

theorem lubfun
  let cU: class U
  let cK: class K
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lubfun.u: |- U = ( lub ` K )


  assert |- Fun U

  proof
    cK
    cvv
    wcel
    #
    cU
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
    vy
    cv
    #
    vx
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
    @4
    vz
    cv
    #
    @6
    wbr
    vy
    @7
    wral
    @5
    @8
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
    cU
    @13
    @0
    @9
    vx
    vy
    vz
    @2
    cU
    cK
    @6
    cvv
    vs
    @2
    eqid
    @6
    eqid
    lubfun.u
    @9
    biid
    @0
    id
    lubfval
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
    cU
    c0
    @15
    cU
    cK
    club
    cfv
    c0
    lubfun.u
    cK
    club
    fvprc
    syl5eq
    funeqd
    mpbiri
    pm2.61i
end
