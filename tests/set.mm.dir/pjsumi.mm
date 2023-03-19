include "chil.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cph.mm"
include "co.mm"
include "cpjh.mm"
include "cva.mm"
include "wceq.mm"
include "wa.mm"
include "chj.mm"
include "osumi.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "adantl.mm"
include "cch.mm"
include "wi.mm"
include "pjcjt2.mm"
include "mp3an12.mm"
include "imp.mm"
include "eqtrd.mm"
include "ex.mm"

theorem pjsumi
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjsumt.1: |- G e. CH
  assume pjsumt.2: |- H e. CH


  assert |- ( A e. ~H -> ( G C_ ( _|_ ` H ) -> ( ( projh ` ( G +H H ) ) ` A ) = ( ( ( projh ` G ) ` A ) +h ( ( projh ` H ) ` A ) ) ) )

  proof
    cA
    chil
    wcel
    #
    cG
    cH
    cort
    cfv
    wss
    #
    cA
    cG
    cH
    cph
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    cA
    cG
    cpjh
    cfv
    cfv
    cA
    cH
    cpjh
    cfv
    cfv
    cva
    co
    #
    wceq
    @0
    @1
    wa
    @4
    cA
    cG
    cH
    chj
    co
    #
    cpjh
    cfv
    #
    cfv
    #
    @5
    @1
    @4
    @8
    wceq
    @0
    @1
    cA
    @3
    @7
    @1
    @2
    @6
    cpjh
    cG
    cH
    pjsumt.1
    pjsumt.2
    osumi
    fveq2d
    fveq1d
    adantl
    @0
    @1
    @8
    @5
    wceq
    #
    cG
    cch
    wcel
    cH
    cch
    wcel
    @0
    @1
    @9
    wi
    pjsumt.1
    pjsumt.2
    cA
    cH
    cG
    pjcjt2
    mp3an12
    imp
    eqtrd
    ex
end
