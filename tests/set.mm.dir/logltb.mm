include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "clog.mm"
include "cres.mm"
include "cfv.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "cr.mm"
include "wf1o.mm"
include "wiso.mm"
include "relogiso.mm"
include "df-isom.mm"
include "mpbi.mm"
include "simpri.mm"
include "wceq.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "mpi.mm"
include "fvres.mm"
include "breqan12d.mm"
include "bitrd.mm"

theorem logltb
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let cN: class N


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A < B <-> ( log ` A ) < ( log ` B ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    clog
    crp
    cres
    #
    cfv
    #
    cB
    @4
    cfv
    #
    clt
    wbr
    #
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    clt
    wbr
    @2
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @10
    @4
    cfv
    #
    @11
    @4
    cfv
    #
    clt
    wbr
    #
    wb
    #
    vy
    crp
    wral
    vx
    crp
    wral
    #
    @3
    @7
    wb
    #
    crp
    cr
    @4
    wf1o
    #
    @17
    crp
    cr
    clt
    clt
    @4
    wiso
    @19
    @17
    wa
    relogiso
    vx
    vy
    crp
    cr
    clt
    clt
    @4
    df-isom
    mpbi
    simpri
    @16
    @18
    cA
    @11
    clt
    wbr
    #
    @5
    @14
    clt
    wbr
    #
    wb
    vx
    vy
    cA
    cB
    crp
    crp
    @10
    cA
    wceq
    #
    @12
    @20
    @15
    @21
    @10
    cA
    @11
    clt
    breq1
    @22
    @13
    @5
    @14
    clt
    @10
    cA
    @4
    fveq2
    breq1d
    bibi12d
    @11
    cB
    wceq
    #
    @20
    @3
    @21
    @7
    @11
    cB
    cA
    clt
    breq2
    @23
    @14
    @6
    @5
    clt
    @11
    cB
    @4
    fveq2
    breq2d
    bibi12d
    rspc2v
    mpi
    @0
    @1
    @5
    @8
    @6
    @9
    clt
    cA
    crp
    clog
    fvres
    cB
    crp
    clog
    fvres
    breqan12d
    bitrd
end
