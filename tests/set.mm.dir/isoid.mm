include "cid.mm"
include "cres.mm"
include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "f1oi.mm"
include "wcel.mm"
include "wa.mm"
include "fvresi.mm"
include "breqan12d.mm"
include "bicomd.mm"
include "rgen2a.mm"
include "df-isom.mm"
include "mpbir2an.mm"

theorem isoid
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( _I |` A ) Isom R , R ( A , A )

  proof
    cA
    cA
    cR
    cR
    cid
    cA
    cres
    #
    wiso
    cA
    cA
    @0
    wf1o
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    @0
    cfv
    #
    @2
    @0
    cfv
    #
    cR
    wbr
    #
    wb
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    f1oi
    @7
    vx
    vy
    cA
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    @6
    @3
    @8
    @9
    @4
    @1
    @5
    @2
    cR
    cA
    @1
    fvresi
    cA
    @2
    fvresi
    breqan12d
    bicomd
    rgen2a
    vx
    vy
    cA
    cA
    cR
    cR
    @0
    df-isom
    mpbir2an
end
