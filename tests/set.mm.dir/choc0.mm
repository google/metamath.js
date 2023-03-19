include "c0h.mm"
include "cort.mm"
include "cfv.mm"
include "chil.mm"
include "cv.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csh.mm"
include "wb.mm"
include "h0elsh.mm"
include "shocel.mm"
include "ax-mp.mm"
include "wi.mm"
include "c0v.mm"
include "hi02.mm"
include "wal.mm"
include "df-ral.mm"
include "elch0.mm"
include "imbi1i.mm"
include "albii.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "ceqsalv.mm"
include "bitri.mm"
include "sylibr.mm"
include "abai.mm"
include "mpbiran2.mm"
include "eqriv.mm"

theorem choc0
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( _|_ ` 0H ) = ~H

  proof
    vx
    c0h
    cort
    cfv
    #
    chil
    vx
    cv
    #
    @0
    wcel
    #
    @1
    chil
    wcel
    #
    @1
    vy
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vy
    c0h
    wral
    #
    wa
    #
    @3
    c0h
    csh
    wcel
    @2
    @8
    wb
    h0elsh
    vy
    @1
    c0h
    shocel
    ax-mp
    @8
    @3
    @3
    @7
    wi
    @3
    @1
    c0v
    csp
    co
    #
    cc0
    wceq
    #
    @7
    @1
    hi02
    @7
    @4
    c0h
    wcel
    #
    @6
    wi
    #
    vy
    wal
    #
    @10
    @6
    vy
    c0h
    df-ral
    @13
    @4
    c0v
    wceq
    #
    @6
    wi
    #
    vy
    wal
    @10
    @12
    @15
    vy
    @11
    @14
    @6
    @4
    elch0
    imbi1i
    albii
    @6
    @10
    vy
    c0v
    c0v
    chil
    ax-hv0cl
    elexi
    @14
    @5
    @9
    cc0
    @4
    c0v
    @1
    csp
    oveq2
    eqeq1d
    ceqsalv
    bitri
    bitri
    sylibr
    @3
    @7
    abai
    mpbiran2
    bitri
    eqriv
end
