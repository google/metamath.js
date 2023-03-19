include "cid.mm"
include "chil.mm"
include "cres.mm"
include "cuo.mm"
include "wcel.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1ofo.mm"
include "ax-mp.mm"
include "fvresi.mm"
include "oveqan12d.mm"
include "rgen2a.mm"
include "elunop.mm"
include "mpbir2an.mm"

theorem idunop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( _I |` ~H ) e. UniOp

  proof
    cid
    chil
    cres
    #
    cuo
    wcel
    chil
    chil
    @0
    wfo
    #
    vx
    cv
    #
    @0
    cfv
    #
    vy
    cv
    #
    @0
    cfv
    #
    csp
    co
    @2
    @4
    csp
    co
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    chil
    chil
    @0
    wf1o
    @1
    chil
    f1oi
    chil
    chil
    @0
    f1ofo
    ax-mp
    @6
    vx
    vy
    chil
    @2
    chil
    wcel
    @4
    chil
    wcel
    @3
    @2
    @5
    @4
    csp
    chil
    @2
    fvresi
    chil
    @4
    fvresi
    oveqan12d
    rgen2a
    vx
    vy
    @0
    elunop
    mpbir2an
end
