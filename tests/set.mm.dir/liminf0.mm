include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "clsi.mm"
include "cxne.mm"
include "clsp.mm"
include "cpnf.mm"
include "wceq.mm"
include "wtru.mm"
include "cc0.mm"
include "cvv.mm"
include "nftru.mm"
include "wcel.mm"
include "0ex.mm"
include "a1i.mm"
include "0red.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cxr.mm"
include "wn.mm"
include "wi.mm"
include "noel.mm"
include "elinel1.mm"
include "con3i.mm"
include "ax-mp.mm"
include "pm2.21.mm"
include "adantl.mm"
include "liminfval3.mm"
include "trud.mm"
include "mpt0.mm"
include "fveq2i.mm"
include "cmnf.mm"
include "limsup0.mm"
include "eqtri.mm"
include "xnegeqi.mm"
include "xnegmnf.mm"
include "3eqtr3i.mm"

theorem liminf0
  let vk: setvar k
  let vx: setvar x


  assert |- ( liminf ` (/) ) = +oo

  proof
    vx
    c0
    vx
    cv
    #
    c0
    cfv
    #
    cmpt
    #
    clsi
    cfv
    #
    vx
    c0
    @1
    cxne
    #
    cmpt
    #
    clsp
    cfv
    #
    cxne
    #
    c0
    clsi
    cfv
    cpnf
    @3
    @7
    wceq
    wtru
    vx
    c0
    @1
    cc0
    cvv
    vx
    nftru
    c0
    cvv
    wcel
    wtru
    0ex
    a1i
    wtru
    0red
    @0
    c0
    cc0
    cpnf
    cico
    co
    #
    cin
    wcel
    #
    @1
    cxr
    wcel
    #
    wtru
    @9
    wn
    #
    @9
    @10
    wi
    @0
    c0
    wcel
    #
    wn
    @11
    @0
    noel
    @9
    @12
    @0
    c0
    @8
    elinel1
    con3i
    ax-mp
    @9
    @10
    pm2.21
    ax-mp
    adantl
    liminfval3
    trud
    @2
    c0
    clsi
    vx
    @1
    mpt0
    fveq2i
    @7
    cmnf
    cxne
    cpnf
    @6
    cmnf
    @6
    c0
    clsp
    cfv
    cmnf
    @5
    c0
    clsp
    vx
    @4
    mpt0
    fveq2i
    limsup0
    eqtri
    xnegeqi
    xnegmnf
    eqtri
    3eqtr3i
end
