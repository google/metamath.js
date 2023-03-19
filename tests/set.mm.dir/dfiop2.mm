include "chio.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "df-iop.mm"
include "wfn.mm"
include "wceq.mm"
include "helch.mm"
include "pjfni.mm"
include "fnresi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "pjch1.mm"
include "fvresi.mm"
include "eqtr4d.mm"
include "rgen.mm"
include "eqfnfv.mm"
include "mpbiri.mm"
include "mp2an.mm"
include "eqtri.mm"

theorem dfiop2
  let vx: setvar x


  assert |- Iop = ( _I |` ~H )

  proof
    chio
    chil
    cpjh
    cfv
    #
    cid
    chil
    cres
    #
    df-iop
    @0
    chil
    wfn
    #
    @1
    chil
    wfn
    #
    @0
    @1
    wceq
    #
    chil
    helch
    pjfni
    chil
    fnresi
    @2
    @3
    wa
    @4
    vx
    cv
    #
    @0
    cfv
    #
    @5
    @1
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @8
    vx
    chil
    @5
    chil
    wcel
    @6
    @5
    @7
    @5
    pjch1
    chil
    @5
    fvresi
    eqtr4d
    rgen
    vx
    chil
    @0
    @1
    eqfnfv
    mpbiri
    mp2an
    eqtri
end
