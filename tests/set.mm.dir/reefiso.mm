include "cr.mm"
include "crp.mm"
include "clt.mm"
include "ce.mm"
include "cres.mm"
include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "reeff1o.mm"
include "wcel.mm"
include "wa.mm"
include "eflt.mm"
include "fvres.mm"
include "breqan12d.mm"
include "bitr4d.mm"
include "rgen2a.mm"
include "df-isom.mm"
include "mpbir2an.mm"

theorem reefiso
  let vx: setvar x
  let vy: setvar y


  assert |- ( exp |` RR ) Isom < , < ( RR , RR+ )

  proof
    cr
    crp
    clt
    clt
    ce
    cr
    cres
    #
    wiso
    cr
    crp
    @0
    wf1o
    vx
    cv
    #
    vy
    cv
    #
    clt
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
    clt
    wbr
    #
    wb
    #
    vy
    cr
    wral
    vx
    cr
    wral
    reeff1o
    @7
    vx
    vy
    cr
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    wa
    @3
    @1
    ce
    cfv
    #
    @2
    ce
    cfv
    #
    clt
    wbr
    @6
    @1
    @2
    eflt
    @8
    @9
    @4
    @10
    @5
    @11
    clt
    @1
    cr
    ce
    fvres
    @2
    cr
    ce
    fvres
    breqan12d
    bitr4d
    rgen2a
    vx
    vy
    cr
    crp
    clt
    clt
    @0
    df-isom
    mpbir2an
end
