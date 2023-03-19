include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cop.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cfv.mm"
include "df-ov.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "wceq.mm"
include "opelxpi.mm"
include "fvres.mm"
include "syl.mm"
include "cc.mm"
include "recn.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2an.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem remetdval
  let cA: class A
  let cB: class B
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A D B ) = ( abs ` ( A - B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cD
    co
    #
    cA
    cB
    cop
    #
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    #
    cres
    #
    cfv
    #
    cA
    cB
    cmin
    co
    cabs
    cfv
    #
    @3
    @4
    cD
    cfv
    @8
    cA
    cB
    cD
    df-ov
    @4
    cD
    @7
    remet.1
    fveq1i
    eqtri
    @2
    @8
    @4
    @5
    cfv
    #
    @9
    @2
    @4
    @6
    wcel
    @8
    @10
    wceq
    cA
    cB
    cr
    cr
    opelxpi
    @4
    @6
    @5
    fvres
    syl
    @2
    @10
    cA
    cB
    @5
    co
    #
    @9
    cA
    cB
    @5
    df-ov
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @11
    @9
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    @5
    @5
    eqid
    cnmetdval
    syl2an
    syl5eqr
    eqtrd
    syl5eq
end
