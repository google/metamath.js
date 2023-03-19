include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "wrex.mm"
include "eqid.mm"
include "pjeq.mm"
include "mpbii.mm"
include "simpld.mm"

theorem axpjcl
  let cA: class A
  let cH: class H
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( projh ` H ) ` A ) e. H )

  proof
    cH
    cch
    wcel
    cA
    chil
    wcel
    wa
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cH
    wcel
    #
    cA
    @1
    vx
    cv
    cva
    co
    wceq
    vx
    cH
    cort
    cfv
    wrex
    #
    @0
    @1
    @1
    wceq
    @2
    @3
    wa
    @1
    eqid
    vx
    cA
    @1
    cH
    pjeq
    mpbii
    simpld
end
